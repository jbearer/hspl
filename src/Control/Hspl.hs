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
    Hspl
  , Term
  , Goal
  , Clause
  -- * Building HSPL programs
  , HsplBuilder
  , ClauseBuilder
  , hspl
  -- ** Defining predicates
  , def
  , (|-)
  , (?)
  -- *** Typed predicates
  -- | Predicates can be foward declared with a type annotation to allow the compiler to infer types
  -- whenever the predicate is applied.
  , PredDecl
  , decl
  -- ** Special predicates
  -- | Some predicates have special semantics. These can appear as goals on the right-hand side of
  -- '|-', but they can never be the object of a 'def' statement on the left-hand side.
  , (|=|)
  , (|\=|)
  , (|==|)
  , (|\==|)
  , lnot
  , is
  -- * Running HSPL programs
  , ProofResult
  , runHspl
  , runHspl1
  , runHsplN
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

-- | The type encapsulating an HSPL program.
type Hspl = Ast.Program

-- | A clause is a logical disjunction of one or more predicates. Each definition of a predicate
-- (see 'def') generates one 'Clause' in the resulting 'Hspl' program.
type Clause = Ast.HornClause

-- | A monad for appending 'Clause's to an 'Hspl' program.
type HsplBuilder = Writer [Clause]

-- | A monad for appending 'Goal's to the definition of a 'Clause'.
type ClauseBuilder = Writer [Goal]

-- | Overloaded functions for constructing predicates in various contexts.
class PredApp a b c | a b -> c where
  -- | Predicate application. @pred? term@ is a goal that succeeds if the predicate @pred@ applied
  -- to @term@ is true.
  (?) :: a -> b -> c

instance TermData a => PredApp String a (ClauseBuilder ()) where
  name? arg = tell [PredGoal $ Ast.predicate name arg]

instance (TermData b, TermEntry a, a ~ HSPLType b) => PredApp (PredDecl a) b (ClauseBuilder ()) where
  name? arg = unDecl name ? arg

instance (TermData b, TermEntry a, a ~ HSPLType b) => PredApp (PredDef a) b (HsplBuilder ()) where
  name? arg = tell [Ast.HornClause (Ast.predicate (unDef name) arg) []]

instance (TermData a) => PredApp UntypedPredDef a (HsplBuilder ()) where
  name? arg = tell [Ast.HornClause (Ast.predicate (unUDef name) arg) []]

-- | The type of a forward declaration of a predicate. 'PredDecl's are created using 'decl' and are
-- suitable only for applying a predicate with '(?)'.
newtype PredDecl a = Decl { unDecl :: String }

-- | Give a forward declaration of a predicate. This is never required; however, using 'decl' with
-- a type annotation can allow for more effective use of type inference. For example, if we define
--
-- @
--  cons = decl "cons" :: PredDecl (Int, [Int], [Int])
-- @
--
-- Then the predicate application
--
-- @
--  cons? (v"x", v"xs", v"x" <:> v"xs")
-- @
--
-- is equivalent to
--
-- @
--  "cons"? (int "x", int \* "xs", int "x" <:> int \* "xs")
-- @
decl :: String -> PredDecl a
decl = Decl

-- | The type of a predicate definition with a particular name. 'PredDef's are created using 'def'
-- and are suitable only for defining a predicate with '(?)' and '(|-)'.
newtype PredDef a = Def { unDef :: String }

-- | The type of a predicate definition with unkown type. The type of the predicate will be inferred
-- from the type of the argument to which it is applied.
newtype UntypedPredDef = UDef { unUDef :: String }

-- | Overloaded functions for predicate definitions.
class Definition a b | a -> b where
  -- | Define a new predicate. The predicate has a name and an argument, which is pattern matched
  -- whenever a goal with a matching name is encountered. The definition may be empty, in which case
  -- the predicate succeeds whenever pattern matching succeeds. Otherwise, the definition consists of
  -- the '|-' operator followed by a @do@ block containing a sequence of predicate applications. If
  -- pattern matching on the argument succeeds, then each line of the @do@ block is tried as a
  -- subgoal; if all subgoals succeed, the predicate succeeds.
  --
  -- In terms of first-order logic, the relationship between the predicate and the definition is one
  -- of implication; the conjunction of all of the goals in the definition implies the predicate.
  --
  -- Example:
  --
  -- @
  --  def "mortal"? int "x" |- do
  --    "human"? int "x"
  -- @
  --
  -- This defines a predicate @mortal(X)@, which is true if @human(X)@ is true; in other words,
  -- this definition defines the relationship @human(X) => mortal(X)@.
  --
  -- This function is polymorphic in its first argument (the name of the predicate to define).
  -- If that argument is a 'String', as above, then the type of the argument to the predicate is
  -- ambiguous and must be deduced from the argument itself.
  --
  -- If, however, the first argument to 'def' is a 'PredDecl' (result of 'decl') then the argument
  -- to the predicate must have the corresponding type, and the Haskell compiler can infer that
  -- type. The following declaration is equivalent to the previous example:
  --
  -- @
  --  mortal = decl "mortal" :: PredDecl Int
  --  def mortal? auto "x" |- do
  --    "human"? int "x"
  -- @
  def :: a -> b

instance Definition (PredDecl a) (PredDef a) where
  def = Def . unDecl

instance Definition String UntypedPredDef where
  def = UDef

-- | Indicates the beginning of the definition of a predicate.
infixr 0 |-
(|-) :: HsplBuilder () -> ClauseBuilder a -> HsplBuilder ()
p |- gs =
  let [Ast.HornClause goal []] = execWriter p
      goals = execWriter gs
  in tell [Ast.HornClause goal goals]

-- | Unify two terms. The predicate succeeds if and only if unification succeeds.
(|=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> ClauseBuilder ()
t1 |=| t2 = tell [Ast.CanUnify (toTerm t1) (toTerm t2)]

-- | Negation of '|=|'. The predicate @t1 |\\=| t2@ succeeds if and only if @t1 |=| t2@ fails. No
-- new bindings are created.
(|\=|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> ClauseBuilder ()
t1 |\=| t2 = lnot $ t1 |=| t2

-- | Test if two terms are unified. This predicate succeeds if and only if the two terms are
-- identical under the current unfier. No new bindings are created.
(|==|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> ClauseBuilder ()
t1 |==| t2 = tell [Ast.Identical (toTerm t1) (toTerm t2)]

-- | Negation of '|==|'. The predicate @t1 |\\==| t2@ succeeds if and only if @t1 |==| t2@ fails.
-- No new bindings are created.
(|\==|) :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> ClauseBuilder ()
t1 |\==| t2 = lnot $ t1 |==| t2

-- | Logical negation. @lnot p@ is a predicate which is true if and only if the predicate @p@ is
-- false. @lnot@ does not create any new bindings.
lnot :: ClauseBuilder a -> ClauseBuilder ()
lnot p = case execWriter p of
  [g] -> tell [Not g]
  _ -> error "lnot must be applied to exactly one predicate."

-- | Evaluate an arithmetic expression. The right-hand side is evaluated, and the resulting numeric
-- constant is then unified with the left-hand side. Note that 'is' will cause a run-time error if
-- the right-hand side expression contains unbound variables, or is not a valid arithmetic
-- expression. An expression may contain constants, instantiated variables, and combinations thereof
-- formed using '|+|', '|-|', etc.
infix 1 `is`
is :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> ClauseBuilder ()
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

-- | Construct an HSPL program.
hspl :: HsplBuilder a -> Hspl
hspl builder = Ast.addClauses (execWriter builder) Ast.emptyProgram

-- | Query an HSPL program for a given goal. The 'ProofResult's returned can be inspected using
-- functions like `getAllSolutions`, `searchProof`, etc.
runHspl :: Hspl -> ClauseBuilder a -> [ProofResult]
runHspl program gs = case execWriter gs of
  [PredGoal goal] -> Solver.runHspl program goal
  _ -> error "Please specify exactly one predicate to prove."

-- | Query an HSPL program for a given goal. If a proof is found, stop immediately instead of
-- backtracking to look for additional solutions. If no proof is found, return 'Nothing'.
runHspl1 :: Hspl -> ClauseBuilder a -> Maybe ProofResult
runHspl1 program gs = case runHsplN 1 program gs of
  [] -> Nothing
  (res:_) -> Just res

-- | Query an HSPL program for a given goal. Stop after @n@ solutions are found.
runHsplN :: Int -> Hspl -> ClauseBuilder a -> [ProofResult]
runHsplN n program gs = case execWriter gs of
  [PredGoal goal] -> Solver.runHsplN n program goal
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
