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
    TermEntry
  , TermData (..)
  -- * AST
  -- $ast
  -- ** Variables
  , Var (..)
  , varType
  -- ** Terms
  , Term (..)
  , termType
  , fromTerm
  , constructor
  -- ** Predicates
  , Predicate (..)
  , predicate
  , predType
  -- ** Goals
  , Goal (..)
  -- ** Clauses
  , HornClause (..)
  , clauseType
  -- * Miscellaneous utilites
  -- ** Tuple construction and deconstruction
  -- $tuples
  , Tuple (..)
  , thead
  , ttail
  -- ** Error reporting
  , wrap
  ) where

import           Data.Data
import           Data.List
import           Data.Maybe

{- $typeSystem
HSPL implements a type system which prevents unification of terms with different types. The HSPL
type system intersects to a great degree with Haskell's native type system, and most Haskell values
can be used as constants in HSPL. That said, throughout this documentation, we will make the
distinction between Haskell types and HSPL types, since these are not all the same. For instance,
the abstract representation of a variable in HSPL is a Haskell data type of type @Variable a@, where
@a@ represents the HSPL type of the variable.
-}

-- | Class for types which can be represented by a term. The only purpose of this class is to give
-- a succinct method for constraining the superclasses required of any HSPL type.
class ( Typeable a
      , Data a
      , Eq a
#ifdef SHOW_TERMS
      , Show a
#endif
      ) => TermEntry a where {}
instance ( Typeable a
         , Data a
         , Eq a
#ifdef SHOW_TERMS
         , Show a
#endif
         ) => TermEntry a

-- |
-- The class of types which can be deconstructed and converted to a 'Term'. For example,
--
-- >>> toTerm True
-- Constant (True)
--
-- >>> toTerm (True, "foo")
-- Tup (Constant (True)) (List [Constant ('F'), Constant ('o'), Constant ('o')])
--
-- >>> :t toTerm (True, "foo")
-- toTerm (True, "Foo") :: Term (Bool, [Char])
class TermEntry (HSPLType a) => TermData a where
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
instance TermEntry a => TermData (Var a) where
  type HSPLType (Var a) = a
  toTerm = Variable

-- Terms can trivially be converted to Terms
instance TermEntry a => TermData (Term a) where
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
HSPLPrimitive(Double)

#undef HSPLPrimitive

-- Tuples
instance (TermData a, TermData b) => TermData (a, b) where
  type HSPLType (a, b) = (HSPLType a, HSPLType b)
  toTerm t = Tup (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c) => TermData (a, b, c) where
  type HSPLType (a, b, c) = (HSPLType a, HSPLType b, HSPLType c)
  toTerm t = Tup (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d) => TermData (a, b, c, d) where
  type HSPLType (a, b, c, d) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d)
  toTerm t = Tup (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d, TermData e) => TermData (a, b, c, d, e) where
  type HSPLType (a, b, c, d, e) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e)
  toTerm t = Tup (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d, TermData e, TermData f) => TermData (a, b, c, d, e, f) where
  type HSPLType (a, b, c, d, e, f) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e, HSPLType f)
  toTerm t = Tup (toTerm $ thead t) (toTerm $ ttail t)

instance (TermData a, TermData b, TermData c, TermData d, TermData e, TermData f, TermData g) => TermData (a, b, c, d, e, f, g) where
  type HSPLType (a, b, c, d, e, f, g) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e, HSPLType f, HSPLType g)
  toTerm t = Tup (toTerm $ thead t) (toTerm $ ttail t)

-- Lists
instance (TermData a, TermEntry (HSPLType a)) => TermData [a] where
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
  -- | Internal constructor used to generate variables which are not equal to any user-defined ones.
  Fresh :: Typeable a => Int -> Var a
  deriving (Typeable)
deriving instance Eq (Var a)
deriving instance Ord (Var a)

instance Show (Var a) where
  show (Var x) = x ++ " :: " ++ show (typeOf (undefined :: a))
  show (Fresh x) = "_" ++ show x ++ " :: " ++ show (typeOf (undefined :: a))

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
  Constructor :: (TermEntry a, TermEntry b) => (a -> b) -> Term a -> Term b

  -- | A product type (i.e. a tuple). We define tuples inductively with a head and a tail, which
  -- allows the simple representation of any tuple with just this one constructor.
  Tup :: (Tuple a, TermEntry a, TermEntry (Head a), TermEntry (Tail a)) =>
         Term (Head a) -> Term (Tail a) -> Term a

  -- | A primitive constant.
  Constant :: TermEntry a => a -> Term a

  -- | A cons cell.
  List :: TermEntry a => Term a -> Term [a] -> Term [a]

  -- | An emtpy list (base case for the 'List' constructor)
  Nil :: TermEntry a => Term [a]

  -- | A variable which can unify with any 'Term' of type @a@.
  Variable :: TermEntry a => Var a -> Term a

  -- | An arithmetic sum of two 'Term's.
  Sum :: (Num a, TermEntry a) => Term a -> Term a -> Term a

  -- | An arithmetic difference of 'Term's.
  Difference :: (Num a, TermEntry a) => Term a -> Term a -> Term a

  -- | An arithmetic product of 'Term's.
  Product :: (Num a, TermEntry a) => Term a -> Term a -> Term a

  -- | An arithmetic quotient of 'Term's. The quotient is obtained by floating point (real)
  -- division, and as such the type of the represented value must have an instance for 'Fractional'.
  Quotient :: (Fractional a, TermEntry a) => Term a -> Term a -> Term a

  -- | An arithmetic quotient of 'Term's. The quotient is obtained by integer division, and as such
  -- the type of the represented value must have an instance for 'Integral'.
  IntQuotient :: (Integral a, TermEntry a) => Term a -> Term a -> Term a

  -- | An arithmetic expression representing the remainder when dividing the first 'Term' by the
  -- second.
  Modulus :: (Integral a, TermEntry a) => Term a -> Term a -> Term a

  deriving (Typeable)

#ifdef DEBUG
instance Show (Term a) where
  show (Constructor f t) = "Constructor (" ++ show (constructor f) ++ ") (" ++ show t ++ ")"
  show (Tup t ts) = "Tup (" ++ show t ++ ") (" ++ show ts ++ ")"
  show (List x xs) = "List (" ++ show x ++ ") (" ++ show xs ++ ")"
  show Nil = "Nil"
#ifdef SHOW_TERMS
  show (Constant c) = "Constant (" ++ show c ++ ")"
#else
  show (Constant _) = "Constant"
#endif
  show (Variable v) = "Variable (" ++ show v ++ ")"
  show (Sum t1 t2) = "Sum (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Difference t1 t2) = "Difference (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Product t1 t2) = "Product (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Quotient t1 t2) = "Quotient (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (IntQuotient t1 t2) = "IntQuotient (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Modulus t1 t2) = "Modulus (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
#else
instance Show (Term a) where
  show (Constructor f t) = show (constructor f) ++ " (" ++ show t ++ ")"
  show (Tup t ts) = show t ++ ", " ++ show ts
  show (List x Nil) = show x
  show (List x xs) = show x ++ ", " ++ show xs
  show Nil = "[]"
#ifdef SHOW_TERMS
  show (Constant c) = show c
#else
  show (Constant _) = "c"
#endif
  show (Variable v) = show v
  show (Sum t1 t2) = "(" ++ show t1 ++ ") |+| (" ++ show t2 ++ ")"
  show (Difference t1 t2) = "(" ++ show t1 ++ ") |-| (" ++ show t2 ++ ")"
  show (Product t1 t2) = "(" ++ show t1 ++ ") |*| (" ++ show t2 ++ ")"
  show (Quotient t1 t2) = "(" ++ show t1 ++ ") |/| (" ++ show t2 ++ ")"
  show (IntQuotient t1 t2) = "(" ++ show t1 ++ ") |\\| (" ++ show t2 ++ ")"
  show (Modulus t1 t2) = "(" ++ show t1 ++ ") |%| (" ++ show t2 ++ ")"
#endif

instance Eq (Term a) where
  (==) (Constructor f t) (Constructor f' t') =
    let c = constructor f
        c' = constructor f'
    in case cast t' of
      Just t'' -> c == c' && t == t''
      Nothing -> False

  (==) (Tup t ts) (Tup t' ts') = fromMaybe False $ do
    t'' <- cast t'
    ts'' <- cast ts'
    return $ t == t'' && ts == ts''

  (==) (List x xs) (List y ys) = x == y && xs == ys
  (==) Nil Nil = True

  (==) (Constant t) (Constant t') = t == t'

  (==) (Variable x) (Variable x') = x == x'

  (==) (Sum t1 t2) (Sum t1' t2') = t1 == t1' && t2 == t2'
  (==) (Difference t1 t2) (Difference t1' t2') = t1 == t1' && t2 == t2'
  (==) (Product t1 t2) (Product t1' t2') = t1 == t1' && t2 == t2'
  (==) (Quotient t1 t2) (Quotient t1' t2') = t1 == t1' && t2 == t2'
  (==) (IntQuotient t1 t2) (IntQuotient t1' t2') = t1 == t1' && t2 == t2'
  (==) (Modulus t1 t2) (Modulus t1' t2') = t1 == t1' && t2 == t2'

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
fromTerm :: TermEntry a => Term a -> Maybe a
fromTerm term = case term of
  Constructor f x -> fmap f $ fromTerm x
  Tup t ts -> do
    ut <- fromTerm t
    uts <- fromTerm ts
    return $ tcons ut uts
  List x xs -> do
    ux <- fromTerm x
    uxs <- fromTerm xs
    return $ ux : uxs
  Nil -> Just []
  Constant c -> Just c
  Variable _ -> Nothing
  Sum t1 t2 -> fromBinOp (+) t1 t2
  Difference t1 t2 -> fromBinOp (-) t1 t2
  Product t1 t2 -> fromBinOp (*) t1 t2
  Quotient t1 t2 -> fromBinOp (/) t1 t2
  IntQuotient t1 t2 -> fromBinOp div t1 t2
  Modulus t1 t2 -> fromBinOp mod t1 t2
  where fromBinOp f t1 t2 = do ut1 <- fromTerm t1
                               ut2 <- fromTerm t2
                               return $ f ut1 ut2

-- | Determine the HSPL type of a term.
termType :: forall a. Typeable a => Term a -> TypeRep
termType _ = typeOf (undefined :: a)

-- | A predicate is a truth-valued proposition about 0 or more terms. The positive literal in a
-- 'HornClause' is a predicate.
--
-- In this implementation, all predicates are 1-ary -- they each take a single term. This is
-- sufficient because the generic nature of 'Term' means that the term could encode a product type
-- such as a tuple, or (). Thus, 0-ary predicates have the form @Predicate "foo" (Constant ())@ and
-- n-ary predicates look like @Predicate "bar" (Tup ('a') (Tup ...))@.
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

-- | A 'Goal' is a proposition which can appear as a negative literal in a 'HornClause'.
data Goal =
            -- | A goal which succeeds if the 'Predicate' is true. The predicate is true if for at
            -- least one of the clauses
            --
            -- * The predicate unifies the the positive literal of the 'HornClause'.
            -- * Each 'Goal' which is a negative literal of the 'HornClause' is true.
            PredGoal Predicate [HornClause]
            -- | A goal which succeeds if the two 'Term's can be unified.
          | forall t. TermEntry t => CanUnify (Term t) (Term t)
            -- | A goal which succeeds if the two 'Term's are identical under the current
            -- 'Control.Hspl.Internal.Unification.Unifier'.
          | forall t. TermEntry t => Identical (Term t) (Term t)
            -- | A goal which succeeds only if the inner 'Goal' fails.
          | Not Goal
            -- | A goal which succeeds if the right-hand side, after being evaluated as an
            -- arithmetic expression, unifies with the left-hand side.
          | forall t. TermEntry t => Equal (Term t) (Term t)

instance Show Goal where
  show (PredGoal p _) = show p
  show (CanUnify t1 t2) = show t1 ++ " |=| " ++ show t2
  show (Identical t1 t2) = show t1 ++ " |==| " ++ show t2
  show (Not g) = "lnot (" ++ show g ++ ")"
  show (Equal t1 t2) = show t1 ++ " `is` " ++ show t2

instance Eq Goal where
  (==) (PredGoal p cs) (PredGoal p' cs') = p == p' && cs == cs'
  (==) (CanUnify t1 t2) (CanUnify t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) (Identical t1 t2) (Identical t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) (Not g) (Not g') = g == g'
  (==) (Equal t1 t2) (Equal t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) _ _ = False

-- | A 'HornClause' is the logical disjunction of a single positive literal (a 'Predicate') and 0 or
-- or more negated literals. In this implementation, the negative literals are 'Goal's, the
-- conjunction of which implies the the positive literal.
data HornClause = HornClause Predicate [Goal]
  deriving (Show, Eq)

-- | Determine the HSPL type of a 'HornClause', which is defined to be the type of the positive
-- 'Predicate'.
clauseType :: HornClause -> TypeRep
clauseType (HornClause p _) = predType p

{- $tuples
The 'Tuple' class and associated functions make it easier to work with Haskell tuples in the
HSPL type system, by allowing a single 'Tup' abstract term to account for all tuple types.
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
