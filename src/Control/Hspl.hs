{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraints
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl
Description : Predicate logic programming for Haskell.
Stability   : Experimental

HSPL (Haskell Predicate Logic) is an embedded language that brings logic programming to Haskell.
HSPL uses resolution-based automated theorem proving to make logical deductions, providing
functionality similar to that of logic programming languages like Prolog.

See "Control.Hspl.Examples" for some sample programs.
-}
module Control.Hspl (
  -- * Types
    Term
  , Goal
  , Clause
  , Predicate
  , Termable (..)
  , TermData
  , TermEntry
  , SubTerm
  , NoVariables
  -- * Building HSPL programs
  , GoalWriter (..)
  , execGoalWriter
  , ClauseWriter (..)
  , execClauseWriter
  -- ** Defining predicates
  , predicate
  , semiDetPredicate
  , match
  , (|-)
  , (?)
  -- ** Special predicates
  -- | Some predicates have special semantics. These can appear as goals on the right-hand side of
  -- '|-'.
  , findAll
  , bagOf
  , once
  , cut
  -- *** Unification, identity, equality, and inequality
  , (|=|)
  , (|\=|)
  , is
  , isnt
  , (|==|)
  , (|\==|)
  , (|<|)
  , (|<=|)
  , (|>|)
  , (|>=|)
  -- *** Logical connectives
  , lnot
  , (|||)
  , true
  , false
  -- * Running HSPL programs
  , runHspl
  , runHspl1
  , runHsplN
  -- ** Inspecting results
  , ProofResult
  , searchProof
  , getUnifier
  , getAllUnifiers
  , getSolution
  , getAllSolutions
  , queryVar
  , UnificationStatus (..)
  -- * The HSPL type system
  -- $types
  -- ** Variables
  -- *** The variable constructor
  , Var (Var)
  -- *** Typed constructors
  -- $typedVars
  , bool
  , int
  , integer
  , char
  , double
  , string
  , (\*)
  , auto
  , v
  -- ** Numbers
  -- | HSPL provides special semantics for numeric types. Arithmetic expressions can be created
  -- using the following operators and evaluated using 'is'.
  , (|+|)
  , (|-|)
  , (|*|)
  , (|/|)
  , (|\|)
  , (|%|)
  -- ** Lists
  -- $lists
  , (<:>)
  , (<++>)
  , nil
  , helem
  , hlength
  , hat
  , hdelete
  -- ** ADTs
  -- $adts
  , ($$)
  , enum
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Exception (assert)
import Control.Monad.Writer
import Data.Data

import qualified Control.Hspl.Internal.Ast as Ast
import           Control.Hspl.Internal.Ast ( Var (Var)
                                           , Term
                                           , TermEntry
                                           , TermData
                                           , SubTerm
                                           , Termable (..)
                                           , NoVariables
                                           , Goal (..)
                                           , HSPLType
                                           , AdtTerm (..)
                                           )
import qualified Control.Hspl.Internal.Solver as Solver
import           Control.Hspl.Internal.Solver ( ProofResult
                                              , searchProof
                                              , getUnifier
                                              , getAllUnifiers
                                              , getSolution
                                              , getAllSolutions
                                              )
import           Control.Hspl.Internal.Unification (queryVar, UnificationStatus (..))

-- | A clause is a logical disjunction of one or more predicates. Each definition of a predicate
-- (see 'def') generates one 'Clause' in the resulting 'Hspl' program.
type Clause = Ast.HornClause

-- | A monad for appending 'Goal's to the definition of a 'Clause'.
newtype GoalWriter a = GW { unGW :: Writer Goal a }
  deriving (Functor, Applicative, Monad, MonadWriter Goal)

-- | Extract the 'Goal' from a 'GoalWriter'.
execGoalWriter :: GoalWriter a -> Goal
execGoalWriter = execWriter . unGW

-- | A monad for appending alternative 'Clause's to a 'Predicate'. This monad creates a list of
-- functions waiting for a predicate name. When applied to a string, they produce clauses whose
-- positive literals has that name.
newtype ClauseWriter t a = CW { unCW :: Writer [String -> Clause] a }
  deriving (Functor, Applicative, Monad, MonadWriter [String -> Clause])

-- | Extract a list of 'Clause' constructors from a 'ClauseWriter'.
execClauseWriter :: ClauseWriter t a -> [String -> Clause]
execClauseWriter = execWriter . unCW

-- | Predicate application. @pred? term@ is a goal that succeeds if the predicate @pred@ applied
-- to @term@ is true.
infix 9 ?
(?) :: TermData a => Predicate (HSPLType a) -> a -> GoalWriter ()
p? arg = let g = Ast.PredGoal (Ast.predicate (predName p) arg) (definitions p)
         in if semiDet p then tell (Once g) else tell g

-- | A declaration of a predicate with a given name and set of alternatives. Parameterized by the
-- type of the argument to which the predicate can be applied.
data Predicate a = Predicate { predName :: String, definitions :: [Clause], semiDet :: Bool }

-- | Declare and define a new predicate with a given name. This function takes a block containing
-- one or more definitions ('match' statements). For example, we define a predicate called "odd"
-- which succeeds when the argument is an odd 'Int':
--
-- @
--  odd = predicate "odd" $ do
--    match(1 :: Int)
--    match(int "x") |- do
--      int "y" `is` int "x" |-| (2 :: Int)
--      odd? int "y"
-- @
--
-- There are a few restrictions on the name assigned to a predicate. First, the name must not
-- contain whitespace. It can, however, contain any non-whitespace characters you want.
--
-- Second, the name must be unique among all predicates with the same type. If two predicates of the
-- same type have the same name, the program may exhibit unexpected behavior without explicitly
-- failing. Good practice is to give a predicate the same name as the Haskell identifier to which it
-- is assigned, as in the example above. If that convention is followed, the Haskell compiler can be
-- used to enforce the uniquencess of the names. Unfortunately, this only works for predicates
-- declared at the top level. For predicates defined in a @let@ expression or a @where@ clause, dot-
-- syntax can be used to ensure name uniqueness, as in
--
-- @
--  foo = predicate "foo" $
--    match(char "x") |- bar?(char "x")
--    where bar = predicate "foo.bar" $ match 'a'
-- @
--
-- It is also worth saying a few words about the type of this function. It is polymorphic in the
-- type of the argument to which the predicate can be applied. If no type annotation is given, the
-- compiler will attempt to infer this type from the type of the 'match' statements in the
-- definition. If a type annotation is given, then the type of variables in the 'match' statements
-- can be inferred, allowing the use of 'auto' or 'v'.
--
-- If the GHC extension @ScopedTypeVariables@ is used, type annotations can also be used to declare
-- generic predicates, like so:
--
-- @
--  elem :: forall a. TermEntry a => Predicate (a, [a])
--  elem = predicate "elem" $ do
--    let va x = Var "x" :: Var a
--    match (va "x", va "x" <:> v "xs")
--    match (va "y", va "x" <:> v"xs") |- elem? (v"y", v"xs")
-- @
--
-- Note that the generic type must be an instance of 'TermEntry'.
predicate :: String -> ClauseWriter t b -> Predicate t
predicate name gs = Predicate { predName = name
                              , definitions = map ($name) $ execClauseWriter gs
                              , semiDet = False
                              }

-- | Declare and define a new semi-deterministic predicate. The usage is exactly the same as that of
-- 'predicate'. However, predicates created with 'semiDetPredicate' are semi-deterministic, meaning
-- they succeed at most once.
semiDetPredicate :: String -> ClauseWriter t b -> Predicate t
semiDetPredicate name cw = (predicate name cw) { semiDet = True }

-- | Make a statement about when a 'Predicate' holds for inputs of a particular form. A 'match'
-- statement succeeds when the input can unify with the argument to 'match'. When attempting to
-- prove a predicate, HSPL will first find all definitions of the predicate which match the goal,
-- and then try to prove any subgoals of the 'match' statement (which can be specified using '|-').
match :: TermData a => a -> ClauseWriter (HSPLType a) ()
match t = tell [\p -> Ast.HornClause (Ast.predicate p $ toTerm t) Top]

-- | Indicates the beginning of a list of subgoals in a predicate definition. Whenever the 'match'
-- statement on the left-hand side of '|-' succeeds, the solver attempts to prove all subgoals on
-- the right-hand side. If it is successful, then the overall predicate succeeds.
infixr 0 |-
(|-) :: ClauseWriter t a -> GoalWriter b -> ClauseWriter t ()
p |- gs =
  let [f] = execClauseWriter p
      goal = execGoalWriter gs
      addGoal name = let Ast.HornClause prd ogGoal = f name
                     in assert (ogGoal == Top) $ Ast.HornClause prd goal
  in tell [addGoal]

-- | Unify a list with all the alternatives of a given template. @findAll template goal list@ works
-- as follows:
--
-- 1. The given goal is proven nondeterministically, yielding a list of 'ProofResult's.
-- 2. From each 'ProofResult', the 'Unifier' is extracted and applied to @template@, yielding a list
--    of 'Term's.
-- 3. The solver attempts to unify the list of 'Term's with @list@. If successful, the goal succeeds
--    and @list@ is bound to the list of 'Term's.
--
-- Note that 'findAll' succeeds even if the inner goal fails, so long as @list@ unifies with an
-- empty list.
findAll :: (TermData a, TermData c, HSPLType c ~ [HSPLType a]) =>
           a -> GoalWriter b -> c -> GoalWriter ()
findAll x gw xs =
  let g = execGoalWriter gw
  in tell $ Alternatives (toTerm x) g (toTerm xs)

-- | Like 'findAll', but fails if the inner goal fails.
bagOf :: forall a b c. (TermData a, TermData c, HSPLType c ~ [HSPLType a]) =>
         a -> GoalWriter b -> c -> GoalWriter ()
bagOf x gw xs =
  let p :: Predicate [HSPLType a]
      p = predicate "bagOf" $
            match(v"x" <:> v"xs") |- findAll x gw (v"x" <:> v"xs")
  in p? xs

-- | Convert a possibly non-deterministic goal into a semi-deterministic goal. If a goal @g@
-- succeeds at all, then the goal @once g@ succeeds exactly once, and the result is the first
-- solution of @g@. If @g@ fails, then @once g@ also fails.
once :: GoalWriter a -> GoalWriter ()
once gw = tell $ Once $ execGoalWriter gw

-- | Discard all choicepoints created since entering the current predicate.
cut :: GoalWriter ()
cut = tell Cut

-- | Unify two terms. The predicate succeeds if and only if unification succeeds.
infix 2 |=|
(|=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
t1 |=| t2 = tell $ Ast.CanUnify (toTerm t1) (toTerm t2)

-- | Negation of '|=|'. The predicate @t1 |\\=| t2@ succeeds if and only if @t1 |=| t2@ fails. No
-- new bindings are created.
infix 2 |\=|
(|\=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
t1 |\=| t2 = lnot $ t1 |=| t2

-- | Test if two terms are unified. This predicate succeeds if and only if the two terms are
-- identical under the current unifier. No new bindings are created.
is :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
is t1 t2 = tell $ Ast.Identical (toTerm t1) (toTerm t2)

-- | Negation of 'is'. The predicate @t1 `isnt` t2@ succeeds if and only if @t1 `is` t2@ fails.
-- No new bindings are created.
isnt :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
isnt t1 t2 = lnot $ t1 `is` t2

-- | Logical negation. @lnot p@ is a predicate which is true if and only if the predicate @p@ is
-- false. @lnot@ does not create any new bindings.
lnot :: GoalWriter a -> GoalWriter ()
lnot p =
  let g = execGoalWriter p
  in tell $ Not g

-- | Logical disjunction. @p ||| q@ is a predicate which is true if either @p@ is true or @q@ is
-- true. @|||@ will backtrack over alternatives, so if both @p@ and @q@ are true, it will produce
-- multiple solutions.
infixl 1 |||
(|||) :: GoalWriter a -> GoalWriter b -> GoalWriter ()
gw1 ||| gw2 =
  let g1 = execGoalWriter gw1
      g2 = execGoalWriter gw2
  in tell $ Or g1 g2

-- | A predicate which always succeeds.
true :: GoalWriter ()
true = tell Top

-- | A predicate which always fails.
false :: GoalWriter ()
false = tell Bottom

-- | Simplify a term and test for equality. The right-hand side is evaluated, and the resulting
-- constant is then unified with the left-hand side. Note that '|==|' will cause a run-time error if
-- the right-hand side expression contains unbound variables.
infix 2 |==|
(|==|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
a |==| b = tell $ Equal (toTerm a) (toTerm b)

-- | Negation of '|==|'. The predicate @t1 |\\==| t2@ succeeds if and only if @t1 |==| t2@ fails. No
-- new bindings are created. Note that in order to prove @t1 |\\==| t2@, the system will attempt to
-- prove @t1 |==| t2@ and then negate the result. This means that @t1 |\\==| t2@ will still result
-- in a runtime error if @t2@ has uninstantiated variables.
infix 2 |\==|
(|\==|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
a |\==| b = lnot $ a |==| b

-- | Simplify terms and test for inequality. Both terms are evaluated and the resulting constants
-- are compared using '<'. No new bindings are created. Note that a runtime error will be raised if
-- /either/ term contains uninstantiated variables.
infix 2 |<|
(|<|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
         a -> b -> GoalWriter ()
t1 |<| t2 = tell $ LessThan (toTerm t1) (toTerm t2)

-- | Simplify terms and test for equality or inequality. The right-hand term is evaluated first. It
-- is then unified with the left-hand side. If unification succeeds, the predicate succeeds and the
-- inequality check is not performed. This means that, while the right-hand side must not contain
-- uninstantaited variables, the left-hand side can so long as it unifies with the results of the
-- right-hand side. However, if unification fails, then the left-hand side /will/ be evaluated in
-- order to perform the inequality check, at which point a runtime error will be raised if the left-
-- hand side contains uninstantiated variables.
infix 2 |<=|
(|<=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
         a -> b -> GoalWriter ()
t1 |<=| t2 = t1 |==| t2 ||| (t1 |\==| t2 >> t1 |<| t2)

-- | Simplify terms and test for inequality. @t1 |>| t2@ is equivalent to @t2 |<| t1@. See '|<|' for
-- details.
infix 2 |>|
(|>|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
         a -> b -> GoalWriter ()
t1 |>| t2 = t2 |<| t1

-- | Similar to '|<=|'; however, @t1 |>=| t2@ is /not/ equivalent to @t2 |<=| t1@. The difference is
-- in the order of evaluation. Like '|<=|', '|>=|' evaluates its right-hand argument first and then
-- short-circuits if the result unifies with the left-hand side. The left-hand side is only
-- evaluated if unification fails.
infix 2 |>=|
(|>=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
         a -> b -> GoalWriter ()
t1 |>=| t2 = t1 |==| t2 ||| (t1 |\==| t2 >> t1 |>| t2)

-- | Addition. Create a term representing the sum of two terms.
infixl 8 |+|
(|+|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Num (HSPLType a)) =>
         a -> b -> Term (HSPLType a)
a |+| b = Ast.Sum (toTerm a) (toTerm b)

-- | Subtraction. Create a term representing the difference of two terms.
infixl 8 |-|
(|-|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Num (HSPLType a)) =>
         a -> b -> Term (HSPLType a)
a |-| b = Ast.Difference (toTerm a) (toTerm b)

-- | Multiplication. Create a term representing the product of two terms.
infixl 9 |*|
(|*|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Num (HSPLType a)) =>
         a -> b -> Term (HSPLType a)
a |*| b = Ast.Product (toTerm a) (toTerm b)

-- | Division. Create a term representing the quotient of two terms. Both operands must be of
-- 'Fractional' type.
infixl 9 |/|
(|/|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Fractional (HSPLType a)) =>
         a -> b -> Term (HSPLType a)
a |/| b = Ast.Quotient (toTerm a) (toTerm b)

-- | Integer divison. Create a term representing the the quotient of two terms, truncated towards 0.
-- Both operands must be of 'Integral' type.
infixl 9 |\|
(|\|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Integral (HSPLType a)) =>
         a -> b -> Term (HSPLType a)
a |\| b = Ast.IntQuotient (toTerm a) (toTerm b)

-- | Modular arithmetic. Create a term representing the remainer when dividing the first term by the
-- second. Both operands must be of 'Integral' type.
infixl 9 |%|
(|%|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Integral (HSPLType a)) =>
         a -> b -> Term (HSPLType a)
a |%| b = Ast.Modulus (toTerm a) (toTerm b)

-- | Query an HSPL program for a given goal. The 'ProofResult's returned can be inspected using
-- functions like `getAllSolutions`, `searchProof`, etc.
runHspl :: GoalWriter a -> [ProofResult]
runHspl gs =
  let g = execGoalWriter gs
  in Solver.runHspl g

-- | Query an HSPL program for a given goal. If a proof is found, stop immediately instead of
-- backtracking to look for additional solutions. If no proof is found, return 'Nothing'.
runHspl1 :: GoalWriter a -> Maybe ProofResult
runHspl1 gs = case runHsplN 1 gs of
  [] -> Nothing
  (res:_) -> Just res

-- | Query an HSPL program for a given goal. Stop after @n@ solutions are found.
runHsplN :: Int -> GoalWriter a -> [ProofResult]
runHsplN n gs =
  let g = execGoalWriter gs
  in Solver.runHsplN n g

{- $types
HSPL implements a type system which prevents unification of terms with different types. The HSPL
type system intersects to a great degree with Haskell's native type system, and most Haskell values
can be used as terms in HSPL. Compound Haskell types like lists, tuples, and ADTs can even be
decontructed and pattern matched in HSPL.
-}

{- $typedVars
Because HSPL programs are statically typed, the type of every variable must be known at compile
time. HSPL variables have the type @Var a@, where @a@ is the type represented by the variable. For
example, a variable of type @Var Int@ could unify with any term of type @Term Int@.

The 'Var'
constructor has type @String -> Var a@, where the type variable @a@ is intentionally left ambiguous.
It is possible to create variables of any type using this constructor by adding a type annotation.
For instance, @Var "x" :: Var Int@ is an @Int@ variable.

To cut down on the wordiness of such declarations, C-style type annotation functions are provided
which make it possible to say, for example, @int "x"@. This expression is equivalent to the previous
example. These convenience functions are provided for some primitive types. It is also possible to
add your own, as in

@
  myType :: String -> Var MyType
  myType = Var
@

Note the importance of the type annotation in the above declaration; @myType@ is simply an alias for
the 'Var' constructor, but the type annotation restricts the types that can be constructed using
@myType@ and thus provides the compiler enough information to use @myType@ without further
annotations.
-}

-- | Construct a 'String' variable.
string :: String -> Var String
string = Var

-- | Construct an 'Int' variable.
int :: String -> Var Int
int = Var

-- | Construct an 'Integer' variable.
integer :: String -> Var Integer
integer = Var

-- | Construct a 'Bool' variable.
bool :: String -> Var Bool
bool = Var

-- | Construct a 'Char' variable.
char :: String -> Var Char
char = Var

-- | Contruct a 'Double' variable
double :: String -> Var Double
double = Var

-- | Construct a variable which represents a list of terms.
--
-- >>> char \* "x"
-- x :: [Char]
infixr 9 \*
(\*) :: Typeable a => (String -> Var a) -> String -> Var [a]
(\*) _ = Var

-- | Construct a variable and let the Haskell compiler try to deduce its type.
auto :: Typeable a => String -> Var a
auto = Var

-- | Terser, but less readable, synonym for 'auto'.
v :: Typeable a => String -> Var a
v = auto

{- $adts
Algebraic data types can be used as normal HSPL terms as long as they are instances of 'Termable'.
For example, @auto "x" |=| Just 'a'@ is valid HSPL. It is also possible to embed variables as
subterms in an ADT via the '$$' constructor. See 'Control.Hspl.Examples.adts' for an example.
-}

-- | Apply an ADT constructor to a term. The constructor is uncurried before application, and the
-- term should therefore be a tuple of the right arity. For example,
--
-- @
--  data Tree a = Leaf a | Node a (Tree a) (Tree a)
--    deriving (Show, Eq, Typeable, Data, Generic)
--  instance SubTerm a => Termable Tree a
--
--  t = Node $$ ('a', char "left", char "right")
-- @
--
-- Here @t@ is a term representating a @Tree Char@ whose root is @'a'@ and whose left and right
-- subtrees are represented by the variables @"left"@ and @"right"@.
--
-- Note the classes which must be derived in order to use ADTs with HSPL: 'Eq', 'Typeable', 'Data',
-- and 'Generic', as well as 'Show' if the @ShowTerms@ flag is enabled. Deriving these classes
-- requires the extensions @DeriveDataTypeable@ and @DeriveGeneric@. Also note that if the ADT is
-- parameterized by a type (e.g. @a@) then that type must be an instance of 'SubTerm'.
--
-- If Haskell is unable to derive an instance for 'Generic' (for instance, this may happen with some
-- GADTs) then you can implement 'Termable' yourself, instead of using the defaut implementation.
-- You must implement one method -- 'toTerm' -- and you can do so using '$$'. For example,
--
-- @
--  instance SubTerm a => Termable Tree a where
--    toTerm (Leaf a) = Leaf $$ a
--    toTerm (Tree a l r) = Tree $$ (a, l, r)
-- @
infixr 3 $$
($$) :: AdtTerm f a r => f -> a -> Term r
($$) = adt

-- | Backtrack over all the values of a bounded enumerable type. For example,
--
-- >>> getAllSolutions $ runHspl $ enum? bool "x"
-- [enum(False), enum(True)]
enum :: forall a. (TermEntry a, Bounded a, Enum a) => Predicate a
enum = predicate "enum" $
  match(v"x") |- helem?(v"x" :: Var a, enumFromTo minBound maxBound :: [a])

{- $lists
Lists can also be used as HSPL terms. Lists consisting entirely of constants or of variables can be
created directly from the corresponding Haskell lists. Non-homogeneous lists (lists containing a
combination of constants and variabes) can be created with the '<:>' and '<++>' combinators. These
lists can then be pattern matched against other lists, unifying the variables in each list against
matching elements in the other list. See 'Control.Hspl.Examples.lists' for an example.
-}

-- | Prepend an element to a list of terms. This may be necessary (and ':' insufficient) when the
-- list is inhomogeneous, in that it contains some constant terms and some variables. For example,
--
-- >>> char "x" <:> "foo"
-- x :: Char, 'f', 'o', 'o'
--
-- >>> 'a' <:> auto "x"
-- 'a', x :: [Char]
infixr 9 <:>
(<:>) :: (TermData a, TermData as, [HSPLType a] ~ HSPLType as) => a -> as -> Term (HSPLType as)
t <:> ts = Ast.List $ case Ast.getListTerm $ toTerm ts of
  Left x -> Ast.VarCons (toTerm t) x
  Right xs -> Ast.Cons (toTerm t) xs

-- | Append a list of terms to another list. This may be necessary (and '++' insufficient) when one
-- list contains term constants and another contains variables. For example,
--
-- >>> [char "x", char "y"] <++> "foo"
-- x :: Char, y :: Char, 'f', 'o', 'o'
(<++>) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => [a] -> [b] -> Term [HSPLType a]
[] <++> ts = toTerm ts
(t:ts) <++> ts' = t <:> (ts <++> ts')

-- | A term representing an empty list. Note that for most lists which do not contain variables, the
-- list itself can be used as a term, e.g. @helem? (char "c", ['a', 'b', 'c'])@. However, for empty
-- lists, the compiler cannot tell the difference between a list of type @[a]@ and a list of type
-- @[Var a]@. Either would typecheck, and so the type is ambiguous. (Of course, in HSPL, the
-- semantics would be the same, but GHC doesn't know that). The type annotation for 'nil' informs
-- the compiler that it is an empty list of terms, not variables, and so there is no ambiguity.
nil :: forall a. TermEntry a => Term [a]
nil = toTerm ([] :: [a])

-- | @helem? (x, xs)@ succeeds if @x@ is a member of @xs@. There are three primary modes of use:
-- 1. If both arguments are instantiated, 'helem' can be used to determine if an element is in a
--    given list.
-- 2. If the first argument is a variable, but the second argument is instantiated, 'helem' will
--    nondeterministically bind the variable to each member of the list.
-- 3. If the first argument is instantiated, but the second argument is a variable, 'helem' will
--    generate lists, placing the given element at each position in the list. This usage will
--    succeed infinitely many times.
helem :: forall a. TermEntry a => Predicate (a, [a])
helem = predicate "helem" $ do
  match (v"x", v"x" <:> v"xs")
  match (v"x", v"y" <:> v"xs") |- helem? (v"x" :: Var a, v"xs")

-- | @hlength? (xs, l)@ succeeds if @l@ is the length of @xs@. If @l@ is a variable, it is bound to
-- the length of the list.
hlength :: forall a. TermEntry a => Predicate ([a], Int)
hlength = predicate "hlength" $ do
  match ([] :: [a], 0 :: Int)
  match (v"x" <:> v"xs", v"l") |- do
    hlength? (v"xs" :: Var [a], v"l2")
    int "l" |==| int "l2" |+| (1 :: Int)

-- | Delete matching elements from a list. @hdelete? (xs, x, ys)@ succeeds when @ys@ is a list
-- containing all elements from @xs@ except those which unify with @x@.
hdelete :: forall a. TermEntry a => Predicate ([a], a, [a])
hdelete = predicate "hdelete" $
  match (v"in", v"elem", v"out") |-
    findAll (v"x" :: Var a) (select? (v"in", v"elem", v"x")) (v"out")
  where select :: Predicate ([a], a, a)
        select = predicate "hdelete.select" $
                    match (v"xs", v"ignore", v"x") |- do
                      helem? (v"x" :: Var a, v"xs")
                      v"x" |\=| (v"ignore" :: Var a)

-- | @hat? (i, xs, x)@ succeeds if @x@ is the element of @xs@ at position @i@ (counting starts at
-- 0). There are three primary modes of use:
-- 1. If @xs@ and @x@ are instantiated, but @i@ is a variable, 'hat' will bind @i@ to the index of
--    @x@.
-- 2. If @i@ and @xs@ are instantiated, but @x@ is a variable, 'hat' will bind @x@ to the element of
--    @xs@ at position @i@.
-- 3. If neither @i@ nor @x@ are instantiated, 'hat' will enumerate the list @xs@.
hat :: forall a. TermEntry a => Predicate (Int, [a], a)
hat = predicate "hat" $ do
  match (0 :: Int, v"x" <:> v"xs", v"x")
  match (v"i", v"x" <:> v"xs", v"y") |- do
    hat? (v"j", v"xs" :: Var [a], v"y")
    int "i" |==| int "j" |+| (1 :: Int)
