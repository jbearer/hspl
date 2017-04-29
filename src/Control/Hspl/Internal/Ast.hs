{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Interal.Ast
Description : Abstract representations of the various logic primitives understood by HSPL.
Stability   : Internal

This module defines the various primitives that compose the language of predicate logic, such as
'Term's, 'Predicate's, and @Clauses@. In truth, we define a subset of predicate logic where clauses
are required to be Horn clauses (those with exactly one positive literal). This simplifying
assumption greatly increases the efficiency with which a resolution solver can be implemented
without unduly weakening the expressive power of the language.

This module also provides the basis of a type system which allows most Haskell types, including
user-defined ADTs, to be used as 'Term's.
-}
module Control.Hspl.Internal.Ast (
  -- * Type system
  -- $typeSystem
    TermData (..)
  -- * AST
  -- $ast
  , Var (..)
  , Term (..)
  , Predicate (..)
  , HornClause (..)
  , Program
  -- * Functions for building a program
  , predicate
  , emptyProgram
  , addClause
  , addClauses
  -- * Functions for inspecting a program
  , varType
  , termType
  , predType
  , clauseType
  , findClauses
  , fromTerm
  , constructor
  -- * Miscellaneous utilites
  -- ** Tuple construction and deconstruction
  -- $tuples
  , Tuple (..)
  , thead
  , ttail
  -- ** Error reporting
  , wrap
  ) where

import           Control.Monad.State
import           Data.Data
import           Data.List
import qualified Data.Map       as M
import           Data.Maybe

{- $typeSystem
HSPL implements a type system which prevents unification of terms with different types. The HSPL
type system intersects to a great degree with Haskell's native type system, and most Haskell values
can be used as constants in HSPL. That said, throughout this documentation, we will make the
distinction between Haskell types and HSPL types, since these are not all the same. For instance,
the abstract representation of a variable in HSPL is a Haskell data type of type @Variable a@, where
@a@ represents the HSPL type of the variable.
-}

-- |
-- The class of types which can be deconstructed and converted to a 'Term'. For example,
--
-- >>> toTerm True
-- Constant (True)
--
-- >>> toTerm (True, "foo")
-- Product (Constant (True)) (List [Constant ('F'), Constant ('o'), Constant ('o')])
--
-- >>> :t toTerm (True, "foo")
-- toTerm (True, "Foo") :: Term (Bool, [Char])
class ( Data (HSPLType a)
      , Eq (HSPLType a)
#ifdef SHOW_TERMS
      , Show (HSPLType a)
#endif
      ) => TermData a where

  -- | A map from Haskell types to HSPL types. This is a many-to-one type function which takes
  --
  -- * @Var a@ to @HSPLType a@
  -- * tuples @(a1, ..., an)@ to @(HSPLType a1, ..., HSPLType an)@
  -- * @[a]@ to @[HSPLType a]@
  -- * @Term a@ to @a@
  type HSPLType a

  -- | Convert a Haskell value to a 'Term'.
  toTerm :: a -> Term (HSPLType a)

-- Variables
instance ( Data a
         , Eq a
#ifdef SHOW_TERMS
         , Show a
#endif
         ) => TermData (Var a) where
  type HSPLType (Var a) = a
  toTerm = Variable

-- Terms can trivially be converted to Terms
instance ( Data a
         , Eq a
#ifdef SHOW_TERMS
         , Show a
#endif
         ) => TermData (Term a) where
  type HSPLType (Term a) = a
  toTerm = id

-- Primitives (Haskell types which are not deconstructed further). We can always add more of these.
#define HSPLPrimitive(a) \
instance TermData a where \
  type HSPLType a = a; \
  toTerm = Constant

HSPLPrimitive(())
HSPLPrimitive(Char)
HSPLPrimitive(Bool)
HSPLPrimitive(Int)
HSPLPrimitive(Integer)

#undef HSPLPrimitive

-- Tuples
instance (TermData a, TermData b) => TermData (a, b) where
  type HSPLType (a, b) = (HSPLType a, HSPLType b)
  toTerm t = Product (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c) => TermData (a, b, c) where
  type HSPLType (a, b, c) = (HSPLType a, HSPLType b, HSPLType c)
  toTerm t = Product (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d) => TermData (a, b, c, d) where
  type HSPLType (a, b, c, d) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d)
  toTerm t = Product (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d, TermData e) => TermData (a, b, c, d, e) where
  type HSPLType (a, b, c, d, e) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e)
  toTerm t = Product (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d, TermData e, TermData f) => TermData (a, b, c, d, e, f) where
  type HSPLType (a, b, c, d, e, f) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e, HSPLType f)
  toTerm t = Product (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d, TermData e, TermData f, TermData g) => TermData (a, b, c, d, e, f, g) where
  type HSPLType (a, b, c, d, e, f, g) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e, HSPLType f, HSPLType g)
  toTerm t = Product (toTerm $ thead t) (toTerm $ ttail t)

-- Lists
instance TermData a => TermData [a] where
  type HSPLType [a] = [HSPLType a]
  toTerm [] = Nil
  toTerm (x:xs) = List (toTerm x) (toTerm xs)

{- $ast
HSPL's abstract syntax is an abstract representation of first-order predicate logic, comprised of
variables, terms, predicates, and clauses.
-}

-- | A variable is a term which unifies with any other 'Term'.
data Var a where
  Var :: Typeable a => String -> Var a
  deriving (Typeable)
deriving instance Eq (Var a)
deriving instance Ord (Var a)

instance Show (Var a) where
  show (Var x) = x ++ " :: " ++ show (typeOf (undefined :: a))

-- | Determine the HSPL type of a variable.
varType :: forall a. Typeable a => Var a -> TypeRep
varType _ = typeOf (undefined :: a)

{- |
The abstract representation of a term. Terms correspond to elements in the domain of a model. In
formal predicate logic, they can be variables, constant symbols, and function symbols applied to one
or more terms.

In this implementation, a @Term@ can be thought of as a destructuring of an arbitrary Haskell type.
For any inductively defined type @a@, the corresponding @Term@ may be a constant (a value of type
@a@) or a variable, or it may be a "partial value" of type @a@, where one or more recursive children
of @a@ is replaced with a variable.

For example, consider the following user-defined type:

@
  data Tree a = Leaf a | Tree a (Tree a) (Tree a)
@

Corresponding terms may have any of the following structures:

* A constant @Tree@:

> Tree 42
>   Leaf 1
>   Leaf 100

* A tree where one child is a variable @x@ which will unify with any subtree:

> Tree 42
>   Var "x"
>   Leaf 100

* A variable "y" which will unify with any tree:

> Var "y"
-}
data Term a where
  -- | An application of an ADT constructor to a single argument. This allows representing arbitrary
  -- ADTs by uncurring the constructors. Note that the first argument /must/ be an ADT constructor,
  -- any function with the right type will not do. This is checked at runtime. See 'constructor' for
  -- details.
  Constructor :: ( Typeable a
                 , Data b
                 , Eq b
#ifdef SHOW_TERMS
                 , Show a
                 , Show b
#endif
                 ) => (a -> b) -> Term a -> Term b

  -- | A product type (i.e. a tuple). We define tuples inductively with a head and a tail, which
  -- allows the simple representation of any tuple with just this one constructor.
  Product :: (Tuple a, Typeable (Head a), Typeable (Tail a)) => Term (Head a) -> Term (Tail a) -> Term a

  -- | A primitive constant.
  Constant :: ( Data a
              , Eq a
#ifdef SHOW_TERMS
              , Show a
#endif
              ) => a -> Term a

  -- | A cons cell.
  List :: ( Data a
          , Eq a
#ifdef SHOW_TERMS
          , Show a
#endif
          ) => Term a -> Term [a] -> Term [a]

  -- | An emtpy list (base case for the 'List' constructor)
  Nil :: ( Data a
         , Eq a
#ifdef SHOW_TERMS
         , Show a
#endif
         ) => Term [a]

  -- | A variable which can unify with any 'Term' of type @a@.
  Variable :: ( Data a
              , Eq a
#ifdef SHOW_TERMS
              , Show a
#endif
              ) => Var a -> Term a
  deriving (Typeable)

#ifdef DEBUG
instance Show (Term a) where
  show (Constructor f t) = "Constructor (" ++ show (constructor f) ++ ") (" ++ show t ++ ")"
  show (Product t ts) = "Product (" ++ show t ++ ") (" ++ show ts ++ ")"
  show (List x xs) = "List (" ++ show x ++ ") (" ++ show xs ++ ")"
  show Nil = "Nil"
#ifdef SHOW_TERMS
  show (Constant c) = "Constant (" ++ show c ++ ")"
#else
  show (Constant _) = "Constant"
#endif
  show (Variable v) = "Variable (" ++ show v ++ ")"
#else
instance Show (Term a) where
  show (Constructor f t) = show (constructor f) ++ " (" ++ show t ++ ")"
  show (Product t ts) = show t ++ ", " ++ show ts
  show (List x Nil) = show x
  show (List x xs) = show x ++ ", " ++ show xs
  show Nil = "[]"
#ifdef SHOW_TERMS
  show (Constant c) = show c
#else
  show (Constant _) = "c"
#endif
  show (Variable v) = show v
#endif

instance Eq (Term a) where
  (==) (Constructor f t) (Constructor f' t') =
    let c = constructor f
        c' = constructor f'
    in case cast t' of
      Just t'' -> c == c' && t == t''
      Nothing -> False

  (==) (Product t ts) (Product t' ts') = fromMaybe False $ do
    t'' <- cast t'
    ts'' <- cast ts'
    return $ t == t'' && ts == ts''

  (==) (List x xs) (List y ys) = x == y && xs == ys
  (==) Nil Nil = True

  (==) (Constant t) (Constant t') = t == t'

  (==) (Variable x) (Variable x') = x == x'

  (==) _ _ = False

-- | Wrap a string to a given line length.
wrap :: Int -> String -> [String]
-- Implementation sourced from https://gist.github.com/yiannist/4546899
wrap maxWidth text = reverse (lastLine : accLines)
  where (accLines, lastLine) = foldl handleWord ([], "") (words text)
        handleWord (acc, line) word
          -- 'word' fits fine; append to 'line' and continue.
          | length line + length word <= maxWidth = (acc, word `append` line)
          -- 'word' doesn't fit anyway; split awkwardly.
          | length word > maxWidth                =
            let (line', extra) = splitAt maxWidth (word `append` line)
            in  (line' : acc, extra)
          -- 'line' is full; start with 'word' and continue.
          | otherwise                             = (line : acc, word)
        append word ""   = word
        append word line = line ++ " " ++  word

-- | Get a representation of the ADT constructor @f@. This function requires that the constructor
-- of @f x@ can be determined without evaluating @x@. This is possible if @f@ is the constructor
-- itself, or a very simple alias (like @uncurry Constr@).
--
-- However, if @f@ is a function which may
-- use one of several constructors to build the ADT depending on its input, then the input will have
-- to be evaluated to determine the relevant constructor. Because we need to be able to get the
-- constructor for 'Term's which may have HSPL variables as their argument, we cannot afford to rely
-- on evaluating the function. Therefore, using such complex functions as constructors will result
-- in a runtime error.
constructor :: (Typeable a, Typeable b, Data b) => (a -> b) -> Constr
constructor f = toConstr $ f $ error $ intercalate "\n" $ wrap 80 $ unwords
  [ "Constructor " ++ show (typeOf f) ++ " could not be determined."
  , "The data constructor used in building terms must be knowable without evaluating the term."
  , "In some cases, this means that using a function a -> b as a constructor for a Term b is not"
  , "sufficient, because the compiler does not know which constructor will be used when the"
  , "function is evaluated."
  , "Possible fix: use the data constructor itself, rather than a function alias."
  ]

-- | Convert an HSPL 'Term' back to the Haskell value represented by the term, if possible. If the
-- term contains no variables, then this function always succeeds. If the term contains any
-- variables, then the Haskell value cannot be determined and the result is 'Nothing'.
fromTerm :: Term a -> Maybe a
fromTerm (Constructor f x) = fmap f $ fromTerm x
fromTerm (Product t ts) = do
  ut <- fromTerm t
  uts <- fromTerm ts
  return $ tcons ut uts
fromTerm (List x xs) = do
  ux <- fromTerm x
  uxs <- fromTerm xs
  return $ ux : uxs
fromTerm Nil = Just []
fromTerm (Constant c) = Just c
fromTerm (Variable _) = Nothing

-- | Determine the HSPL type of a term.
termType :: forall a. Typeable a => Term a -> TypeRep
termType _ = typeOf (undefined :: a)

-- | A predicate is a truth-valued proposition about 0 or more terms. In this implementation, all
-- predicates are 1-ary -- they each take a single term. This is sufficient because the generic
-- nature of 'Term' means that the term could encode a product type such as a tuple, or (). Thus,
-- 0-ary predicates have the form @Predicate "foo" (Constant ())@ and n-ary predicates look like
-- @Predicate "bar" (Product ('a') (Product ...))@.
data Predicate = forall f. Typeable f => Predicate String (Term f)

instance Show Predicate where
  show (Predicate name args) = name ++ "(" ++ show args ++ ")"

instance Eq Predicate where
  Predicate p t == Predicate p' t' = case cast t' of
    Just t'' -> p == p' && t == t''
    Nothing -> False

-- | Smart constructor for building 'Predicate's out of Haskell types.
predicate :: TermData a => String -> a -> Predicate
predicate s a = Predicate s (toTerm a)

-- | Determine the HSPL type of a 'Predicate', which is defined to be the type of the 'Term' to
-- which it is applied.
predType :: Predicate -> TypeRep
predType (Predicate _ t) = termType t

-- | A 'HornClause' is the logical disjunction of a single positive literal (a 'Predicate') and 0 or
--   or more negated literals (a literal which is true if and only if the corresponding 'Predicate'
--   is false).
data HornClause = HornClause Predicate [Predicate]
  deriving (Show, Eq)

-- | Determine the HSPL type of a 'HornClause', which is defined to be the type of the positive
-- 'Predicate'.
clauseType :: HornClause -> TypeRep
clauseType (HornClause p _) = predType p

-- | The abstract representation of an HSPL program. Sets of 'HornClause's can be indexed by their
-- type, and each matching set can be indexed by the name of the positive 'Predicate'.
type Program = M.Map TypeRep (M.Map String [HornClause])

-- | A program containing no clauses.
emptyProgram :: Program
emptyProgram = M.empty

-- | Add a clause to a program.
addClause :: HornClause -> Program -> Program
addClause c@(HornClause (Predicate name _) _) m =
  let ty = clauseType c
      innerM = M.findWithDefault M.empty ty m
      cs = M.findWithDefault [] name innerM
      innerM' = M.insert name (c : cs) innerM
      m' = M.insert ty innerM' m
  in m'

-- | Syntactic sugar for multiple calls to 'addClause'.
addClauses :: [HornClause] -> Program -> Program
addClauses cs m = m'
  where (_, m') = runState comp m
        comp = forM cs $ \c -> modify $ addClause c

-- | Return all 'HornClause's which have the same name and type as the given 'Predicate'.
findClauses :: Predicate -> Program -> [HornClause]
findClauses p@(Predicate name _) m =
  let ty = predType p
      innerM = M.findWithDefault M.empty ty m
      cs = M.findWithDefault [] name innerM
  in cs

{- $tuples
The 'Tuple' class and associated functions make it easier to work with Haskell tuples in the
HSPL type system, by allowing a single 'Product' abstract term to account for all tuple types.
-}

-- | A class supporting overloaded list-like operations on tuples.
class Tuple a where
  -- | The type of the first element of the tuple.
  type Head a

  -- | The type of the tuple containing all elements but the first.
  type Tail a

  -- | Prepend an element to a tuple.
  tcons :: Head a -> Tail a -> a

  -- | Split a tuple into a head and a tail.
  tuncons :: a -> (Head a, Tail a)

-- | Get the first element of a tuple.
thead :: Tuple a => a -> Head a
thead t = let (x, _) = tuncons t in x

-- | Get the tuple containg all elements but the first.
ttail :: Tuple a => a -> Tail a
ttail t = let (_, xs) = tuncons t in xs

instance Tuple (a, b) where
  type Head (a, b) = a
  type Tail (a, b) = b
  tcons a b = (a, b)
  tuncons (a, b) = (a, b)

#define TUPLE(xs) \
instance Tuple (x, xs) where \
  type Head (x, xs) = x; \
  type Tail (x, xs) = (xs); \
  tcons x (xs) = (x, xs); \
  tuncons (x, xs) = (x, (xs)); \

#define X ,

TUPLE(a X b)
TUPLE(a X b X c)
TUPLE(a X b X c X d)
TUPLE(a X b X c X d X e)
TUPLE(a X b X c X d X e X f)
TUPLE(a X b X c X d X e X f X g)

#undef TUPLE
#undef X
