{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif
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
  , def
  , (|-)
  , ($$)
  -- * Running HSPL programs
  , ProofResult
  , (?)
  , (!?)
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
  , string
  , (|*|)
  , auto
  -- ** Lists
  -- $lists
  , (<:>)
  , (<++>)
  -- ** ADTs
  -- $adts
  , (|$|)
  ) where

import Control.Monad.Writer
import Data.Data
import Data.Tuple.Curry
import Data.Tuple.OneTuple

import qualified Control.Hspl.Internal.Ast as Ast
import           Control.Hspl.Internal.Ast (Var (Var), Term, TermData(..))
import qualified Control.Hspl.Internal.Solver as Solver
import           Control.Hspl.Internal.Solver ( Goal
                                              , ProofResult
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

-- | Predicate application. @pred $$ term@ is a goal that succeeds if the predicate @pred@ applied
-- to @term@ is true.
($$) :: TermData a => String -> a -> ClauseBuilder ()
name $$ arg = tell [Ast.predicate name arg]

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
--  def "mortal" (Var "x" :: Var Int) |- do
--    "human" $$ (Var "x" :: Var Int)
-- @
--
-- This defines a predicate @mortal(X)@, which is true if @human(X)@ is true; in other words,
-- this definition defines the relationship @human(X) => mortal(X)@.
def :: TermData a => String -> a -> HsplBuilder ()
def name arg = tell [Ast.HornClause (Ast.predicate name arg) []]

-- | Indicates the beginning of the definition of a predicate.
infixr 0 |-
(|-) :: HsplBuilder () -> ClauseBuilder a -> HsplBuilder ()
p |- gs =
  let [Ast.HornClause goal []] = execWriter p
      goals = execWriter gs
  in tell [Ast.HornClause goal goals]

-- | Construct an HSPL program.
hspl :: HsplBuilder a -> Hspl
hspl builder = Ast.addClauses (execWriter builder) Ast.emptyProgram

-- | Query an HSPL program for a given goal. The 'ProofResult's returned can be inspected using
-- functions like `getAllSolutions`, `searchProof`, etc.
infixr 0 ?
(?) :: Hspl -> ClauseBuilder a -> [ProofResult]
program ? g =
  let [goal] = execWriter g
  in Solver.runHspl program goal

-- | Query an HSPL program for a given goal. If a proof is found, stop immediately instead of
-- backtracking to look for additional solutions. If no proof is found, return 'Nothing'.
infixr 0 !?
(!?) :: Hspl -> ClauseBuilder a -> Maybe ProofResult
program !? g =
  let [goal] = execWriter g
      results = Solver.runHsplN 1 program goal
  in case results of
    [] -> Nothing
    _ -> Just $ head results

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

-- | Construct a variable which represents a list of terms.
--
-- >>> char |*| "x"
-- x :: [Char]
infixr 9 |*|
(|*|) :: Typeable a => (String -> Var a) -> String -> Var [a]
(|*|) _ = Var

-- | Construct a variable and let the Haskell compiler try to deduce its type.
auto :: Typeable a => String -> Var a
auto = Var

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
Algebraic data types can be used as HSPL terms via the '|$|' constructor. See
'Control.Hspl.Examples.adts' for an example.
-}

-- | Apply an ADT constructor to a term. The constructor is uncurried before application, and the
-- term should therefore be a tuple of the right arity. For example,
--
-- @
--  data Tree a = Leaf a | Node a (Tree a) (Tree a)
--    deriving (Show, Eq, Typeable, Data)
--
--  t = Node |$| ('a', char "left", char "right")
-- @
--
-- Here @t@ is a term representating a @Tree Char@ whose root is @'a'@ and whose left and right
-- subtrees are represented by the variables @"left"@ and @"right"@. Note the classes which must be
-- derived in order to use ADTs with HSPL: 'Eq', 'Typeable', and 'Data', as well as 'Show' if the
-- @ShowTerms@ flag is enabled. Deriving these classes requires the extension @DeriveDataTypeable@.
(|$|) :: ( TermData a
         , ToTuple (HSPLType a)
         , Curry (Tuple (HSPLType a) -> r) f
         , Eq r
         , Data r
#ifdef SHOW_TERMS
         , Show r
#endif
         ) =>
     f -> a -> Term r
f |$| x = Ast.Constructor (uncurryN f . toTuple) (toTerm x)

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
