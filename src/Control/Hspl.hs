{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
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
  -- * Building HSPL programs
  , GoalWriter
  , ClauseWriter (..)
  -- ** Defining predicates
  , predicate
  , match
  , (|-)
  , (?)
  -- ** Special predicates
  -- | Some predicates have special semantics. These can appear as goals on the right-hand side of
  -- '|-'.
  , (|=|)
  , (|\=|)
  , (|==|)
  , (|\==|)
  , lnot
  , is
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
  -- ** ADTs
  -- $adts
  , ($$)
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad.Writer
import Data.Data
import Data.Tuple.Curry
import Data.Tuple.OneTuple

import qualified Control.Hspl.Internal.Ast as Ast
import           Control.Hspl.Internal.Ast (Var (Var), Term, TermEntry, TermData(..), Goal(..), HSPLType)
import qualified Control.Hspl.Internal.Solver as Solver
import           Control.Hspl.Internal.Solver ( ProofResult
                                              , searchProof
                                              , getUnifier
                                              , getAllUnifiers
                                              , getSolution
                                              , getAllSolutions
                                              )

-- | A clause is a logical disjunction of one or more predicates. Each definition of a predicate
-- (see 'def') generates one 'Clause' in the resulting 'Hspl' program.
type Clause = Ast.HornClause

-- | A monad for appending 'Goal's to the definition of a 'Clause'.
type GoalWriter = Writer [Goal]

-- | A monad for appending alternative 'Clause's to a 'Predicate'. This monad creates a list of
-- functions waiting for a predicate name. When applied to a string, they produce clauses whose
-- positive literals has that name.
newtype ClauseWriter t a = CW { unCW :: Writer [String -> Clause] a }

instance Functor (ClauseWriter t) where
  fmap f m = CW $ fmap f $ unCW m

instance Applicative (ClauseWriter t) where
  pure = CW . pure
  f <*> g = CW $ unCW f <*> unCW g

instance Monad (ClauseWriter t) where
  m >>= f = CW $ unCW m >>= unCW . f
  return = pure

instance MonadWriter [String -> Clause] (ClauseWriter t) where
  tell = CW . tell
  listen = CW . listen . unCW
  pass = CW . pass . unCW

-- | Predicate application. @pred? term@ is a goal that succeeds if the predicate @pred@ applied
-- to @term@ is true.
(?) :: (TermData b, TermEntry a, a ~ HSPLType b) => Predicate a -> b -> GoalWriter ()
p? arg = tell [Ast.PredGoal (Ast.predicate (predName p) arg) (definitions p)]

-- | A declaration of a predicate with a given name and set of alternatives. Parameterized by the
-- type of the argument to which the predicate can be applied.
data Predicate a = Predicate { predName :: String, definitions :: [Clause] }

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
-- It is worth saying a few words about the type of this function. It is polymorphic in the type of
-- the argument to which the predicate can be applied. If no type annotation is given, the compiler
-- will attempt to infer this type from the type of the 'match' statements in the definition. If a
-- type annotation is given, then the type of variables in the 'match' statements can be inferred,
-- allowing the use of 'auto' or 'v'.
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
predicate name gs = Predicate name (map ($name) $ execWriter $ unCW gs)

-- | Make a statement about when a 'Predicate' holds for inputs of a particular form. A 'match'
-- statement succeeds when the input can unify with the argument to 'match'. When attempting to
-- prove a predicate, HSPL will first find all definitions of the predicate which match the goal,
-- and then try to prove any subgoals of the 'match' statement (which can be specified using '|-').
match :: (TermData a, b ~ HSPLType a) => a -> ClauseWriter b ()
match t = tell [\p -> Ast.HornClause (Ast.predicate p $ toTerm t) []]

-- | Indicates the beginning of a list of subgoals in a predicate definition. Whenever the 'match'
-- statement on the left-hand side of '|-' succeeds, the solver attempts to prove all subgoals on
-- the right-hand side. If it is successful, then the overall predicate succeeds.
infixr 0 |-
(|-) :: ClauseWriter t a -> GoalWriter b -> ClauseWriter t ()
p |- gs =
  let [f] = execWriter $ unCW p
      goals = execWriter gs
      addGoals name = let Ast.HornClause prd ogGoals = f name
                      in Ast.HornClause prd (ogGoals ++ goals)
  in tell [addGoals]

-- | Unify two terms. The predicate succeeds if and only if unification succeeds.
(|=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
t1 |=| t2 = tell [Ast.CanUnify (toTerm t1) (toTerm t2)]

-- | Negation of '|=|'. The predicate @t1 |\\=| t2@ succeeds if and only if @t1 |=| t2@ fails. No
-- new bindings are created.
(|\=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
t1 |\=| t2 = lnot $ t1 |=| t2

-- | Test if two terms are unified. This predicate succeeds if and only if the two terms are
-- identical under the current unfier. No new bindings are created.
(|==|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
t1 |==| t2 = tell [Ast.Identical (toTerm t1) (toTerm t2)]

-- | Negation of '|==|'. The predicate @t1 |\\==| t2@ succeeds if and only if @t1 |==| t2@ fails.
-- No new bindings are created.
(|\==|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
t1 |\==| t2 = lnot $ t1 |==| t2

-- | Logical negation. @lnot p@ is a predicate which is true if and only if the predicate @p@ is
-- false. @lnot@ does not create any new bindings.
lnot :: GoalWriter a -> GoalWriter ()
lnot p = case execWriter p of
  [g] -> tell [Not g]
  _ -> error "lnot must be applied to exactly one predicate."

-- | Evaluate an arithmetic expression. The right-hand side is evaluated, and the resulting numeric
-- constant is then unified with the left-hand side. Note that 'is' will cause a run-time error if
-- the right-hand side expression contains unbound variables, or is not a valid arithmetic
-- expression. An expression may contain constants, instantiated variables, and combinations thereof
-- formed using '|+|', '|-|', etc.
infix 1 `is`
is :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> GoalWriter ()
is a b = tell [Equal (toTerm a) (toTerm b)]

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
runHspl gs = case execWriter gs of
  [g@(PredGoal _ _)] -> Solver.runHspl g
  _ -> error "Please specify exactly one predicate to prove."

-- | Query an HSPL program for a given goal. If a proof is found, stop immediately instead of
-- backtracking to look for additional solutions. If no proof is found, return 'Nothing'.
runHspl1 :: GoalWriter a -> Maybe ProofResult
runHspl1 gs = case runHsplN 1 gs of
  [] -> Nothing
  (res:_) -> Just res

-- | Query an HSPL program for a given goal. Stop after @n@ solutions are found.
runHsplN :: Int -> GoalWriter a -> [ProofResult]
runHsplN n gs = case execWriter gs of
  [g@(PredGoal _ _)] -> Solver.runHsplN n g
  _ -> error "Please specify exactly one predicate to prove."

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

-- Helper type allowing singleton "tuples" and true tuples to be treated somewhat uniformly
type family Tuple a where
  Tuple (a, b, c, d, e, f, g) = (a, b, c, d, e, f, g)
  Tuple (a, b, c, d, e, f) = (a, b, c, d, e, f)
  Tuple (a, b, c, d, e) = (a, b, c, d, e)
  Tuple (a, b, c, d) = (a, b, c, d)
  Tuple (a, b, c) = (a, b, c)
  Tuple (a, b) = (a, b)
  Tuple a = OneTuple a

-- Helper class to convert singleton "tuples" and true tuples to a representation with an instance
-- for Curry.
class ToTuple a where
  toTuple :: a -> Tuple a

instance {-# OVERLAPPABLE #-} (Tuple a ~ OneTuple a) => ToTuple a where
  toTuple = OneTuple

instance {-# OVERLAPPING #-} ToTuple (a1, a2) where
  toTuple = id
instance {-# OVERLAPPING #-} ToTuple (a1, a2, a3) where
  toTuple = id
instance {-# OVERLAPPING #-} ToTuple (a1, a2, a3, a4) where
  toTuple = id
instance {-# OVERLAPPING #-} ToTuple (a1, a2, a3, a4, a5) where
  toTuple = id
instance {-# OVERLAPPING #-} ToTuple (a1, a2, a3, a4, a5, a6) where
  toTuple = id
instance {-# OVERLAPPING #-} ToTuple (a1, a2, a3, a4, a5, a6, a7) where
  toTuple = id

{- $adts
Algebraic data types can be used as HSPL terms via the '$$' constructor. See
'Control.Hspl.Examples.adts' for an example.
-}

-- | Apply an ADT constructor to a term. The constructor is uncurried before application, and the
-- term should therefore be a tuple of the right arity. For example,
--
-- @
--  data Tree a = Leaf a | Node a (Tree a) (Tree a)
--    deriving (Show, Eq, Typeable, Data)
--
--  t = Node $$ ('a', char "left", char "right")
-- @
--
-- Here @t@ is a term representating a @Tree Char@ whose root is @'a'@ and whose left and right
-- subtrees are represented by the variables @"left"@ and @"right"@. Note the classes which must be
-- derived in order to use ADTs with HSPL: 'Eq', 'Typeable', and 'Data', as well as 'Show' if the
-- @ShowTerms@ flag is enabled. Deriving these classes requires the extension @DeriveDataTypeable@.
($$) :: (TermData a, ToTuple (HSPLType a), Curry (Tuple (HSPLType a) -> r) f, TermEntry r) =>
        f -> a -> Term r
f $$ x = Ast.Constructor (uncurryN f . toTuple) (toTerm x)

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
t <:> ts = Ast.List (toTerm t) (toTerm ts)

-- | Append a list of terms to another list. This may be necessary (and '++' insufficient) when one
-- list contains term constants and another contains variables. For example,
--
-- >>> [char "x", char "y"] <++> "foo"
-- x :: Char, y :: Char, 'f', 'o', 'o'
(<++>) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => [a] -> [b] -> Term [HSPLType a]
[] <++> ts = toTerm ts
(t:ts) <++> ts' = Ast.List (toTerm t) (ts <++> ts')
