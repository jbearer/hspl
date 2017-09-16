{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
    HSPLType
  , Termable (..)
  , TermData
  , TermEntry
  , NoVariables
  , SubTerm
  -- * AST
  -- $ast
  -- ** Variables
  , Var (..)
  , varType
  -- ** Terms
  , ListTerm (..)
  , TupleTerm (..)
  , Term (..)
  , termType
  , fromTerm
  , alphaEquivalent
  , getListTerm
  -- *** ADT helpers
  , AdtConstructor (..)
  , AdtArgument (..)
  , AdtTerm (..)
  , reifyAdt
  -- *** Type erasure
  -- | It is occasionally useful to deal with 'Term's of many types as if they were the same type.
  -- These containers and associated utility functions allow for this. Currently, this is used to
  -- represent a list of arguments to be passed to an algebraic data type constructor when calling
  -- 'fromTerm' on a 'Constructor' 'Term'.
  , ErasedTerm (..)
  , termMap
  , ErasedTermEntry (..)
  , termEntryMap
  -- ** Predicates
  , Predicate (..)
  , predicate
  , predType
  -- ** Goals
  , Goal (..)
  -- ** Clauses
  , HornClause (..)
  , clauseType
  ) where

import Control.Monad
import Control.Monad.State
import Data.Data
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid (Monoid (..))
import GHC.Generics
#if __GLASGOW_HASKELL__ < 800
  hiding (Arity)
#endif

import Control.Hspl.Internal.Tuple

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
      , Termable a
      , NoVariables a
      ) => TermEntry a where {}
instance ( Typeable a
         , Data a
         , Eq a
#ifdef SHOW_TERMS
         , Show a
#endif
         , Termable a
         , NoVariables a
         ) => TermEntry a

-- | The class of types which can be converted to a well-typed 'Term' (well-typed meaning
-- @HSPLType a@ is a 'TermEntry'. It would be nice to have @TermEntry (HSPLType a)@ be a superclass
-- of 'Termable'; however, this leads to a non-terminating cycle in the superclasses of 'Termable'
-- and 'TermEntry'. Breaking it into two classes breaks the cycle.
--
-- Conceptually, 'Termable' encodes the behavior of conversion via 'toTerm', while this class
-- encodes the restrictions on the types which should use that behavior. Consequently, a good rule
-- of thumb is to use 'TermData' for constraints in type annotations, and to use 'Termable' when
-- creating an instance for a new term type. Any type which has an instance for 'Termable' and
-- satisfies the necessary constraints ('Data', 'Eq', etc.) will automatically have an instance for
-- 'TermData'.
class (Termable a, TermEntry (HSPLType a)) => TermData a where {}
instance (Termable a, TermEntry (HSPLType a)) => TermData a

-- | Constraint synonym for @a ~ HSPLType a@.
class (a ~ HSPLType a) => NoVariables a where {}
instance (a ~ HSPLType a) => NoVariables a

-- | Constraint for subterms of an ADT when creating a 'Termable' instance. For example,
--
-- @
--  data Tree a = Leaf a | Node a (Tree a) (Tree a)
--    deriving (Show, Eq, Typeable, Data, Generic)
--  instance SubTerm a => Termable Tree a
-- @
class (TermData a, NoVariables a) => SubTerm a where {}
instance (TermData a, NoVariables a) => SubTerm a

-- | A map from Haskell types to HSPL types. The purpose of this function is to collapse @Var a@ and
-- @Term a@ to @a@. Other types have embedded variables and terms collapsed recursively.
--
-- 'HSPLType' does not, at this time, completely accomplish this goal. It works for primitives,
-- tuples, and lists, but not for ADTs; for example, @HSPLType (Maybe (Var a)) ~ Maybe (Var a)@.
-- Ideally, we would have a generic type function which descends recursively through ADTs. However,
-- for the time being, this is sufficient; we disallow creation of terms from ADTs with embedded
-- variables by not providing an instance of 'GenericAdtTerm' for @K1 i (Var a)@.
type family HSPLType a where
  HSPLType (Var a) = a
  HSPLType (Term a) = a
  HSPLType [a] = [HSPLType a]
  HSPLType (a1, a2, a3, a4, a5, a6, a7) =
    (HSPLType a1, HSPLType a2, HSPLType a3, HSPLType a4, HSPLType a5, HSPLType a6, HSPLType a7)
  HSPLType (a1, a2, a3, a4, a5, a6) =
    (HSPLType a1, HSPLType a2, HSPLType a3, HSPLType a4, HSPLType a5, HSPLType a6)
  HSPLType (a1, a2, a3, a4, a5) = (HSPLType a1, HSPLType a2, HSPLType a3, HSPLType a4, HSPLType a5)
  HSPLType (a1, a2, a3, a4) = (HSPLType a1, HSPLType a2, HSPLType a3, HSPLType a4)
  HSPLType (a1, a2, a3) = (HSPLType a1, HSPLType a2, HSPLType a3)
  HSPLType (a1, a2) = (HSPLType a1, HSPLType a2)
  HSPLType a = a

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
class Termable a where
  -- | Convert a Haskell value to a 'Term'.
  toTerm :: a -> Term (HSPLType a)

  default toTerm :: (NoVariables a, TermEntry a, Generic a, GenericAdtTerm (Rep a)) => a -> Term a
  toTerm a
    | isAlgType (dataTypeOf a) = Constructor (toConstr a) $ genericGetArgs $ from a
    | otherwise = error $
#ifdef SHOW_TERMS
                          "Cannot convert " ++ show a ++ " to Term: " ++
#endif
                          "Expected algebraic data type, but found " ++ show (typeOf a) ++ "."

-- Variables
instance TermEntry a => Termable (Var a) where
  toTerm = Variable

-- Terms can trivially be converted to Terms
instance TermEntry a => Termable (Term a) where
  toTerm = id

-- Primitives (Haskell types which are not deconstructed further). We can always add more of these.
#define HSPLPrimitive(a) \
instance Termable a where \
  toTerm = Constant

HSPLPrimitive(())
HSPLPrimitive(Char)
HSPLPrimitive(Bool)
HSPLPrimitive(Int)
HSPLPrimitive(Integer)
HSPLPrimitive(Double)

#undef HSPLPrimitive

-- Tuples
instance (TermData a, TermData b) => Termable (a, b) where
  toTerm (a, b) = Tup $ Tuple2 (toTerm a) (toTerm b)

instance (TermData a, TermData b, TermData c) => Termable (a, b, c) where
  toTerm t = let Tup ts = (toTerm $ ttail t) in Tup $ TupleN (toTerm $ thead t) ts

instance (TermData a, TermData b, TermData c, TermData d) => Termable (a, b, c, d) where
  toTerm t = let Tup ts = (toTerm $ ttail t) in Tup $ TupleN (toTerm $ thead t) ts

instance (TermData a, TermData b, TermData c, TermData d, TermData e) => Termable (a, b, c, d, e) where
  toTerm t = let Tup ts = (toTerm $ ttail t) in Tup $ TupleN (toTerm $ thead t) ts

instance (TermData a, TermData b, TermData c, TermData d, TermData e, TermData f) => Termable (a, b, c, d, e, f) where
  toTerm t = let Tup ts = (toTerm $ ttail t) in Tup $ TupleN (toTerm $ thead t) ts

instance (TermData a, TermData b, TermData c, TermData d, TermData e, TermData f, TermData g) => Termable (a, b, c, d, e, f, g) where
  toTerm t = let Tup ts = (toTerm $ ttail t) in Tup $ TupleN (toTerm $ thead t) ts

-- Lists
instance TermData a => Termable [a] where
  toTerm = List . toListTerm
    where toListTerm [] = Nil
          toListTerm (x:xs) = Cons (toTerm x) (toListTerm xs)

-- Standard ADTs
instance (NoVariables a, TermData a) => Termable (Maybe a)
instance (NoVariables a, TermData a, NoVariables b, TermData b) => Termable (Either a b)

class GenericAdtTerm f where
  genericGetArgs :: f a -> [ErasedTerm]

instance GenericAdtTerm V1 where
  genericGetArgs _ = undefined

instance GenericAdtTerm U1 where
  genericGetArgs _ = []

instance GenericAdtTerm f => GenericAdtTerm (M1 i c f) where
  genericGetArgs (M1 x) = genericGetArgs x

instance (TermData c, NoVariables c) => GenericAdtTerm (K1 i c) where
  genericGetArgs (K1 c) = [ETerm $ toTerm c]

instance (GenericAdtTerm f, GenericAdtTerm g) => GenericAdtTerm (f :*: g) where
  genericGetArgs (f :*: g) = genericGetArgs f ++ genericGetArgs g

instance (GenericAdtTerm f, GenericAdtTerm g) => GenericAdtTerm (f :+: g) where
  genericGetArgs (L1 f) = genericGetArgs f
  genericGetArgs (R1 f) = genericGetArgs f

{- $ast
HSPL's abstract syntax is an abstract representation of first-order predicate logic, comprised of
variables, terms, predicates, and clauses.
-}

-- | A variable is a term which unifies with any other 'Term'.
data Var a where
  -- | A basic named variable.
  Var :: String -> Var a
  -- | A variable without a name. Anonymous variables unify with all terms, but do not create any
  -- bindings.
  Anon :: Var a
  -- | Internal constructor used to generate variables which are not equal to any user-defined ones.
  Fresh :: Int -> Var a
  deriving (Typeable)
deriving instance Show (Var a)
deriving instance Eq (Var a)
deriving instance Ord (Var a)

-- | Determine the HSPL type of a variable.
varType :: forall a. Typeable a => Var a -> TypeRep
varType _ = typeOf (undefined :: a)

-- | Inductive representation of lists.
data ListTerm a where
  -- | A list composed of a single-element head and a smaller list.
  Cons :: TermEntry a => Term a -> ListTerm a -> ListTerm a
  -- | A partial list. Here, the tail of the list is represented by a single variable. This list
  -- will unify with any list of at least one element so long as the first elements unify.
  VarCons :: TermEntry a => Term a -> Var [a] -> ListTerm a
  -- | An empty list.
  Nil :: ListTerm a
deriving instance Show a => Show (ListTerm a)
deriving instance Eq a => Eq (ListTerm a)

-- | Internal representation of a tuple. We define tuples inductively with a head and a tail, which
-- greatly simplifies operations of tuple terms.
data TupleTerm a where
  -- | The base case for a tuple. Notice that the smallest tuple allowed is a tuple of 2 elements,
  -- as is the case with Haskell tuples.
  Tuple2 :: (TermEntry a, TermEntry b) => Term a -> Term b -> TupleTerm (a, b)
  -- | A tuple consisting of a single-element head and a two- or more-element tail.
  TupleN :: (TermEntry a, TupleCons a, TermEntry (Head a), TermEntry (Tail a), TupleCons (Tail a)) =>
            Term (Head a) -> TupleTerm (Tail a) -> TupleTerm a

deriving instance Show a => Show (TupleTerm a)
deriving instance Eq a => Eq (TupleTerm a)

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
  -- | A primitive constant.
  Constant :: TermEntry a => a -> Term a

  -- | A variable which can unify with any 'Term' of type @a@.
  Variable :: TermEntry a => Var a -> Term a

  -- | An application of an ADT constructor to a list of arguments.
  --
  -- Note that the type of the contained term is ambiguous. At reification time, the arguments will
  -- be dynamically casted to the appropriate types and passed to the constructor, and any cast that
  -- fails will result in a runtime error.
  --
  -- Because of this danger, DO NOT USE THIS CONSTRUCTOR DIRECTLY. Instead use the typesafe 'adt'
  -- smart constructor to convert an ADT constructor and tuple of arguments to their type-erased
  -- representations.
  Constructor :: TermEntry a => Constr -> [ErasedTerm] -> Term a

  -- | A term representing a tuple.
  Tup :: (TermEntry a, TupleCons a, TermEntry (Head a), TermEntry (Tail a)) => TupleTerm a -> Term a

  -- | A term representing a list.
  List :: TermEntry a => ListTerm a -> Term [a]

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

instance Show (Term a) where
  show (Constructor c t) = "Constructor (" ++ show c ++ ") (" ++ show t ++ ")"
  show (Tup t) = "Tup (" ++ show t ++ ")"
  show (List l) = "List (" ++ show l ++ ")"
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

instance Eq (Term a) where
  (==) (Constructor c t) (Constructor c' t') = c == c' && t == t'

  (==) (Tup t) (Tup t') = t == t'

  (==) (List l) (List l') = l == l'

  (==) (Constant t) (Constant t') = t == t'

  (==) (Variable x) (Variable x') = x == x'

  (==) (Sum t1 t2) (Sum t1' t2') = t1 == t1' && t2 == t2'
  (==) (Difference t1 t2) (Difference t1' t2') = t1 == t1' && t2 == t2'
  (==) (Product t1 t2) (Product t1' t2') = t1 == t1' && t2 == t2'
  (==) (Quotient t1 t2) (Quotient t1' t2') = t1 == t1' && t2 == t2'
  (==) (IntQuotient t1 t2) (IntQuotient t1' t2') = t1 == t1' && t2 == t2'
  (==) (Modulus t1 t2) (Modulus t1' t2') = t1 == t1' && t2 == t2'

  (==) _ _ = False

-- | Extract the 'ListTerm' representation of a list from a 'Term' parameterized by a list type.
getListTerm :: TermEntry a => Term [a] -> Either (Var [a]) (ListTerm a)
getListTerm (Variable x) = Left x
getListTerm (List xs) = Right xs
getListTerm t = error $ "Unexpected term " ++ show t ++ " of type " ++ show (termType t) ++
                        ". This is most likely an HSPL bug."

-- | Determine if two 'Term's are alpha-equivalent. Terms are alpha-equivalent if there exists an
-- injective renaming of variables in one term which makes it equal to the other term. For example,
--
-- >>> alphaEquivalent (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))
-- True
--
-- >>> alphaEquivalent (toTerm (Var "x" :: Var Char, Var "y" :: Var Char)) (toTerm (Var "a" :: Var Char, Var "a" :: Var Char))
-- False
--
-- >>> alphaEquivalent (toTerm (Var "x" :: Var Char, 'a')) (toTerm (Var "y" :: Var Char, 'b'))
-- False
alphaEquivalent :: TermEntry a => Term a -> Term a -> Bool
alphaEquivalent term1 term2 = isJust $ evalStateT (alpha term1 term2) (M.empty, M.empty)
  where alpha :: TermEntry a => Term a -> Term a ->
                 StateT (M.Map ErasedVar ErasedVar, M.Map ErasedVar ErasedVar) Maybe ()
        alpha (Variable x) (Variable y) = alphaVar x y
        alpha (Constant c) (Constant c')
          | c == c' = return ()
          | otherwise = mzero

        alpha (Constructor c ts) (Constructor c' ts')
          | c == c' = alphaETermList ts ts'
          | otherwise = mzero

        alpha (Tup t) (Tup t') = alphaTup t t'

        alpha (List l) (List l') = alphaList l l'

        alpha (Sum t1 t2) (Sum t1' t2') = alpha t1 t1' >> alpha t2 t2'
        alpha (Difference t1 t2) (Difference t1' t2') = alpha t1 t1' >> alpha t2 t2'
        alpha (Product t1 t2) (Product t1' t2') = alpha t1 t1' >> alpha t2 t2'
        alpha (Quotient t1 t2) (Quotient t1' t2') = alpha t1 t1' >> alpha t2 t2'
        alpha (IntQuotient t1 t2) (IntQuotient t1' t2') = alpha t1 t1' >> alpha t2 t2'
        alpha (Modulus t1 t2) (Modulus t1' t2') = alpha t1 t1' >> alpha t2 t2'

        alpha _ _ = mzero

        alphaVar :: TermEntry a => Var a -> Var a ->
                    StateT (M.Map ErasedVar ErasedVar, M.Map ErasedVar ErasedVar) Maybe ()
        alphaVar Anon _ = return ()
        alphaVar _ Anon = return ()
        alphaVar x y = do (ml, mr) <- get
                          case (M.lookup (EVar x) ml, M.lookup (EVar y) mr) of
                            -- We haven't seen either of these variables for. Make a note that they
                            -- correspond to each other so that if we see either of them again,
                            -- we'll know it better be paired with the other one.
                            (Nothing, Nothing) ->
                              put ( M.insert (EVar x) (EVar y) ml, M.insert (EVar y) (EVar x) mr)
                            -- We've seen both variables before. Check that last time we saw them,
                            -- they were still paired up with each other.
                            (Just (EVar y'), Just (EVar x')) ->
                              case cast (y', x') of
                                Just (y'', x'') | y'' == y && x'' == x -> return ()
                                _ -> mzero
                            -- We've seen one before but not the other. This means that last time we
                            -- saw it, it was paired with some other variable, not the one it's
                            -- paired with this time.
                            _ -> mzero

        alphaETermList :: [ErasedTerm] -> [ErasedTerm] ->
                          StateT (M.Map ErasedVar ErasedVar, M.Map ErasedVar ErasedVar) Maybe ()
        alphaETermList [] [] = return ()
        alphaETermList [] _ = mzero
        alphaETermList _ [] = mzero
        alphaETermList (ETerm t : ts) (ETerm t' : ts') = lift (cast t') >>= alpha t >> alphaETermList ts ts'

        alphaTup :: (TermEntry a, TupleCons a) => TupleTerm a -> TupleTerm a ->
                    StateT (M.Map ErasedVar ErasedVar, M.Map ErasedVar ErasedVar) Maybe ()
        alphaTup (Tuple2 t1 t2) (Tuple2 t1' t2') = alpha t1 t1' >> alpha t2 t2'
        alphaTup (TupleN t ts) (TupleN t' ts') = alpha t t' >> alphaTup ts ts'
        alphaTup _ _ = mzero

        alphaList :: TermEntry a => ListTerm a -> ListTerm a ->
                     StateT (M.Map ErasedVar ErasedVar, M.Map ErasedVar ErasedVar) Maybe ()
        alphaList (Cons t ts) (Cons t' ts') = alpha t t' >> alphaList ts ts'
        alphaList (VarCons t x) (VarCons t' x') = alpha t t' >> alphaVar x x'
        alphaList Nil Nil = return ()
        alphaList _ _ = mzero

-- | Type-erased container for storing 'Var's of any type.
data ErasedVar = forall a. TermEntry a => EVar (Var a)

instance Show ErasedVar where
  show (EVar v) = show v

instance Eq ErasedVar where
  (==) (EVar v) (EVar v') = maybe False (==v) $ cast v'

instance Ord ErasedVar where
  compare (EVar v) (EVar v') = case cast v' of
    Just v'' -> compare v v''
    Nothing -> compare (varType v) (varType v')

-- | Type-erased container for storing 'Term's of any type.
data ErasedTerm = forall a. TermEntry a => ETerm (Term a)

instance Show ErasedTerm where
  show (ETerm t) = show t

instance Eq ErasedTerm where
  (==) (ETerm t) (ETerm t') = maybe False (==t) $ cast t'

-- | Apply a function to the 'Term' contained in an 'ErasedTerm'. The function must be polymorphic
-- over all possible types that the 'Term' could represent.
termMap :: (forall t. TermEntry t => Term t -> r) -> ErasedTerm -> r
termMap f (ETerm t) = f t

-- | Type-erased container for storing all values satisfying the 'TermEntry' constraint.
data ErasedTermEntry = forall a. TermEntry a => ETermEntry a
  deriving (Typeable)

-- | Apply a function to the value contained in an 'ErasedTermEntry'. The function must be
-- polymorphic over all possible 'TermEntry' values.
termEntryMap :: (forall t. TermEntry t => t -> r) -> ErasedTermEntry -> r
termEntryMap f (ETermEntry t) = f t

instance Show ErasedTermEntry where
#ifdef SHOW_TERMS
  show (ETermEntry t) = show t
#else
  show _ = "ETermEntry"
#endif

-- | The class of types which can be used as the argument to an ADT constructor. It has instances
-- for all 'Tuple' types. Curried constructors should use an argument which is the type of the tuple
-- that would be passed to their uncurried counterpart.
class AdtArgument a where
  -- | Convert a tuple of arguments to a type-erased list of 'Term's.
  getArgs :: a -> [ErasedTerm]

-- Singleton tuples
instance (Typeable a, TermData a) => AdtArgument (Tuple a One) where
  getArgs (Singleton a) = [ETerm $ toTerm a]

-- Base case: Many tuple of size two
instance (Typeable a, TermData a, Typeable b, TermData b) => AdtArgument (Tuple (a, b) Many) where
  getArgs (Tuple (a, b)) = [ETerm $ toTerm a, ETerm $ toTerm b]

-- Tuples of size more than two. Convert the head and recurse on the tail
instance  {-# OVERLAPPABLE #-} ( TermData a, TupleCons a
                               , Typeable (Head a), TermData (Head a)
                               , AdtArgument (Tuple (Tail a) Many)
                               ) => AdtArgument (Tuple a Many) where
  getArgs (Tuple a) = ETerm (toTerm $ thead a) : getArgs (Tuple $ ttail a)

-- | The class of types which can be used as an ADT constructor. This includes all curried functions
-- whose ultimate result type is an ADT. In reality, this class has instances for all curried
-- function types, since it is not possible to express in the type system whether a particular type
-- variable is an ADT or not. Attempting to use this class with non-ADT types will fail at runtime.
class AdtConstructor f where
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
  constructor :: f -> Constr

-- Base case: raw value, not a curried function
instance {-# OVERLAPPABLE #-} Data a => AdtConstructor a where
  constructor a
    | isAlgType (dataTypeOf a) = toConstr a
    | otherwise = error $ "Constructor " ++ show (toConstr a) ++ " is not an ADT constructor. " ++
                  "Please only use ADT constructors where expected by HSPL."

-- Curried function: apply the function to a single bogus argument (which should never be evaluated)
-- and recurse on the resulting, smaller function
instance {-# OVERLAPPING #-} AdtConstructor f => AdtConstructor (a -> f) where
  constructor f = constructor $ f indeterminate
    where indeterminate = error $ "ADT constructor could not be determined. The data " ++
                          "constructor used in building terms must be knowable without " ++
                          "evaluating the term. In some cases, this means that using a function " ++
                          "a -> b as a constructor for a Term b is not sufficient, because the " ++
                          "compiler does not know which constructor will be used when the " ++
                          "function is evaluated. Possible fix: use the data constructor " ++
                          "itself, rather than a function alias."

-- | This class provides a smart constructor for creating ADT terms. Unlike the raw 'Constructor'
-- 'Term' constructor, it is typesafe and will not compile if the argument type does not match the
-- (uncurried) function type. The only reason that this is a class, as opposed to a standalone
-- function, is to give clients a succinct way of writing type constraints, without having to
-- duplicate the monstrous type signature of 'adt'. This class has only one instance, for all types
-- which satisfy the constraints of 'adt'.
class AdtTerm f a r | f a -> r where
  -- | Convert a constructor and a tuple of arguments to a 'Term' representing the corresponding
  -- ADT. The constructor must be a function from a tuple (or a singleton) to an ADT. The semantics
  -- of this function are roughly equivalent to uncurrying the given constructor and applying it to
  -- the tuple of arguments. The only difference is that the tuple may contain variables in place of
  -- constants of the same type.
  adt :: f -> a -> Term r

instance forall n f r a. ( n ~ Arity f, r ~ Result f -- Bind shorter names for conciseness
                         , AdtConstructor f
                         , Arg f ~ HSPLType a -- Typecheck the argument
                         , TermEntry r        -- Typecheck the result
                         , Tupleable a n, AdtArgument (Tuple a n)
                         ) => AdtTerm f a r where
  adt f a = Constructor (constructor f) (getArgs (mkTuple a :: Tuple a n))

-- | Reconstruct an algebraic data type from its 'Term' representation. If the list of arguments is
-- too short or too long for the given constructor, or if any element of the list fails to cast to
-- the proper type, a runtime error is thrown.
reifyAdt :: TermEntry r => Constr -> [ErasedTermEntry] -> r
reifyAdt c l =
  let (r, (nargs, overflow)) = runState (fromConstrM mreify c) (0, l)
  in case overflow of
    [] -> r
    _ -> argOverflowError nargs
  where mreify :: forall d. Data d => State (Int, [ErasedTermEntry]) d
        mreify = do (nargs, args) <- get
                    case args of
                      [] -> argUnderflowError
                      (ETermEntry t : ts) ->
                        put (nargs + 1, ts) >>
                        return (fromMaybe (conversionError nargs t) $ cast t)
        conversionError :: forall a b. ( Typeable a
                                       , Typeable b
#ifdef SHOW_TERMS
                                       , Show a
#endif
                                       ) => Int -> a -> b
        conversionError i a = let term =
#ifdef SHOW_TERMS
                                          "(" ++ show a ++ " :: " ++ show (typeOf a) ++ ")"
#else
                                          show (typeOf a)
#endif
                              in error $ "Cannot convert " ++ term ++ " to type " ++
                                 show (typeOf (undefined :: b)) ++ " at position " ++ show i ++
                                 " of the argument list " ++ show l ++ "). " ++
                                 "This is most likely an HSPL bug."
        argUnderflowError :: forall a. a
        argUnderflowError = error $ "Not enough arguments (" ++ show (length l) ++ ") to " ++
                            "constructor " ++ show c ++ ". This is most likely an HSPL bug."
        argOverflowError :: forall a. Int -> a
        argOverflowError n = error $ "Too many arguments to constructor " ++ show c ++ ". " ++
                             "Expected " ++ show n ++ " but found " ++ show (length l) ++ ". " ++
                             "This is most likely an HSPL bug."

-- | Convert an HSPL 'Term' back to the Haskell value represented by the term, if possible. If the
-- term contains no variables, then this function always succeeds. If the term contains any
-- variables, then the Haskell value cannot be determined and the result is 'Nothing'.
fromTerm :: TermEntry a => Term a -> Maybe a
fromTerm term = case term of
  Constructor c arg -> fmap (reifyAdt c) $ forM arg $ \(ETerm t) -> fmap ETermEntry $ fromTerm t
  Tup t -> fromTuple t
  List l -> fromList l
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

        fromTuple :: TupleTerm a -> Maybe a
        fromTuple (Tuple2 t1 t2) = do ut1 <- fromTerm t1
                                      ut2 <- fromTerm t2
                                      return (ut1, ut2)
        fromTuple (TupleN t ts) = do ut <- fromTerm t
                                     uts <- fromTuple ts
                                     return $ tcons ut uts

        fromList :: ListTerm a -> Maybe [a]
        fromList (Cons t ts) = do ut <- fromTerm t
                                  uts <- fromList ts
                                  return $ ut:uts
        fromList Nil = Just []
        fromList _ = Nothing

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
data Predicate = forall f. TermEntry f => Predicate String (Term f)

instance Show Predicate where
  show (Predicate name args) = "Predicate " ++ show name ++ " (" ++ show args ++ ")"

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
            -- | A goal which succeeds if the right-hand side, after being simplified, unifies with
            -- the left-hand side.
          | forall t. TermEntry t => Equal (Term t) (Term t)
            -- | A goal which succeeds if the evaluated left-hand side is less than the evaluated
            -- right-hand side.
          | forall t. (TermEntry t, Ord t) => LessThan (Term t) (Term t)
            -- | A goal which succeeds if the given term is completely unified (that is,
            -- @isJust (fromTerm t) == True@).
          | forall t. TermEntry t => IsUnified (Term t)
            -- | A goal which succeeds if the given term is a variable. Note that this does not mean
            -- the term /contains/ a variable, that would be redundant with @Not (IsUnified t)@.
            -- Rather, for 'IsVariable' to succeed, the term must /be/ a variable.
          | forall t. TermEntry t => IsVariable (Term t)
            -- | A goal which succeeds only if the inner 'Goal' fails.
          | Not Goal
            -- | A goal which succeeds if and only if both subgoals succeed.
          | And Goal Goal
            -- | A goal which succeeds if either subgoal succeeds.
          | Or Goal Goal
            -- | A goal which always succeeds.
          | Top
            -- | A goal which always fails.
          | Bottom
            -- | Similar to Prolog's @findall/3@. @Alternatives template goal bag@ is a goal which
            -- succeeds if @bag@ unifies with the alternatives of @template@ in @goal@.
          | forall t. TermEntry t => Alternatives (Maybe Int) (Term t) Goal (Term [t])
            -- | A goal which succeeds at most once. If the inner goal succeeds multiple times, only
            -- the first result is taken.
          | Once Goal
            -- | A goal with a side-effects. Always succeeds, but causes unexplored choice points
            -- created since the last predicate to be discarded.
          | Cut
            -- | Indicates that the inner 'Goal' should be recorded for future inspection if it is
            -- proven. 'Track' succeeds whenever the inner 'Goal' does.
          | Track Goal
deriving instance Show Goal

instance Eq Goal where
  -- Here we make the assumption that if two predicates have the same name, they have the same
  -- associated clauses. This is necessary because, for recursive predicates (very common and
  -- useful) one of the clauses may contain a reference to the same top-level PredGoal, and so
  -- traversing the clauses to check for equality may not terminate. Note that it is up to the user
  -- to provide names that are unique to each predicate, or else there will be weird behavior
  -- wherever we make this assumption.
  (==) (PredGoal p _) (PredGoal p' _) = p == p'

  (==) (CanUnify t1 t2) (CanUnify t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) (Identical t1 t2) (Identical t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) (Equal t1 t2) (Equal t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) (LessThan t1 t2) (LessThan t1' t2') = case cast (t1', t2') of
    Just t' -> (t1, t2) == t'
    Nothing -> False
  (==) (IsUnified t) (IsUnified t') = maybe False (==t) $ cast t'
  (==) (IsVariable t) (IsVariable t') = maybe False (==t) $ cast t'
  (==) (Not g) (Not g') = g == g'
  (==) (And g1 g2) (And g1' g2') = g1 == g1' && g2 == g2'
  (==) (Or g1 g2) (Or g1' g2') = g1 == g1' && g2 == g2'
  (==) Top Top = True
  (==) Bottom Bottom = True
  (==) (Alternatives n1 x g xs) (Alternatives n2 x' g' xs') = matchN n1 n2 && case cast (x', xs') of
    Just t' -> (x, xs) == t' && g == g'
    Nothing -> False
    where matchN Nothing Nothing = True
          matchN (Just n) (Just n') = n == n'
          matchN _ _ = False
  (==) (Once g) (Once g') = g == g'
  (==) Cut Cut = True
  (==) (Track g) (Track g') = g == g'
  (==) _ _ = False

instance Monoid Goal where
  mappend = And
  mempty = Top

-- | A 'HornClause' is the logical disjunction of a single positive literal (a 'Predicate') and 0 or
-- or more negated literals. In this implementation, the negative /literal/ is a single 'Goal',
-- whose truth implies that of the positive literal. Because a single 'Goal' can be the conjunction
-- of many goals (see 'And'), this is sufficient to represent all Horn clauses.
--
-- We can also represent some clauses which are not strictly Horn clauses, if the negative literal
-- contains an 'Or' subgoal. However, such clauses can always be rewritten as multiple true Horn
-- clauses; we just forego that rewriting for performance and simplicity.
data HornClause = HornClause Predicate Goal
  deriving (Show, Eq)

-- | Determine the HSPL type of a 'HornClause', which is defined to be the type of the positive
-- 'Predicate'.
clauseType :: HornClause -> TypeRep
clauseType (HornClause p _) = predType p
