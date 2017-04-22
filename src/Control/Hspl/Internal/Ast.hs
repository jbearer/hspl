{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Interal.Ast
Description : Abstract representations of the various logic primitives understood by HSPL.

This module defines the various primitives that compose the language of predicate logic, such as
'Term's, 'Predicate's, and @Clauses@. In truth, we define a subset of predicate logic where clauses
are required to be Horn clauses (those with exactly one positive literal). This simplifying
assumption greatly increases the efficiency with which a resolution solver can be implemented
without unduly weakening the expressive power of the language.

This module also provides generic instances of the 'TermData' class, which allows most Haskell
types, including user-defined ADTs, to be cast as 'Term's.
-}
module Control.Hspl.Internal.Ast (
  -- * Type system
  -- $typeSystem
    HSPLType
  , TermData (..)
  , GTermData (..)
  -- * AST
  , Variable (..)
  , TermRep (..)
  , Term (..)
  , Predicate (..)
  , HornClause (..)
  , PredMap
  -- * Functions for building a program
  , var
  , term
  , tconst
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
  ) where

import           Control.Monad.State
import           Data.List
import qualified Data.Map       as M
import           Data.Typeable
import           GHC.Generics

{- $typeSystem
HSPL implements a type system which prevents unification of terms with different types. The HSPL
type system intersects to a great degree with Haskell's native type system, and most Haskell values
can be used as constants in HSPL. That said, throughout this documentation, we will make the
distinction between Haskell types and HSPL types, since these are not all the same. For instance,
the abstract representation of a variable in HSPL is a Haskell data type of type @Variable a@, where
@a@ represents the HSPL type of the variable.
-}

-- | The purpose of this type family is to provide a level of indirection between Haskell types and
-- HSPL types. @HSPLType a@ is the HSPL type of the Haskell type @a@. For most types, these are the
-- same. However, for HSPL variables, the HSPL type of the Haskell type @Variable a@ is @a@ (the
-- type contained by the variable). This family also provides instances for destructuring compound
-- types such as tuples, which allows the embedding of variables within tuples.
type family HSPLType a where
  HSPLType (Variable a) = HSPLType a
  HSPLType [a] = [HSPLType a]
  HSPLType (a, b) = (HSPLType a, HSPLType b)
  HSPLType (a, b, c) = (HSPLType a, HSPLType b, HSPLType c)
  HSPLType (a, b, c, d) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d)
  HSPLType (a, b, c, d, e) = (HSPLType a, HSPLType b, HSPLType c, HSPLType d, HSPLType e)
  HSPLType a = a

{- |
The class of types which can be represented as a 'Term'. Instances of 'TermData' which do not use
the default implementation of 'toTerm' become primitives in the HSPL language. Primitves are types
which can unify with a variable and with equal elements of the same type, but cannot be
destructured. Instances of 'TermData' which use the default implementation can be destructured in
the manner described in the documentation for 'TermRep'.

To use a new user-defined type as an HSPL term, you must provide instances for @Generic@,
@Typeable@, and @Eq@ (and @Show@ if the @ShowTerms@ flag is enabled). These instances can usually be
provided by @deriving@, with the @DeriveGeneric@ extension. You must also provide a default instance
for 'TermData'. As a minimal example:

@
  import GHC.Generics
  import Data.Typeable

  data UserData = UD
    deriving (Typeable, Generic, Eq, Show)

  instance TermData UserData
@

Types contained in your custom type must also be 'TermData', as in:

@
  data Container a = Singleton a
    deriving (Typeable, Generic, Eq, Show)

  instance TermData a => TermData (Container a)
@

This can be made more concise by enabling the @DeriveAnyClass@ extension. Then you can write:

@
  data Container a = Singleton a
    deriving (Typeable, Generic, Eq, Show, TermData)
@

New primitives can also be added to the language:

@
  data Primitive

  instance TermData Primitive where
    toTerm = Const
@

Be very careful when doing so, as adding an ADT as a primitive prevents that type from being
destructured and pattern matched, and will also affect any more complicated types using the new
primitive type.
-}
class ( Typeable (HSPLType a)
      , Eq (HSPLType a)
#ifdef SHOW_TERMS
      , Show (HSPLType a)
#endif
      ) => TermData a where

  -- | Convert a Haskell data type to HSPL's internal representation of a term.
  toTerm :: a -> TermRep

  -- | Default implementation of @toTerm@, which allows destructuring of ADTs.
  default toTerm :: (Generic a, GTermData (Rep a)) => a -> TermRep
  toTerm = gToTerm . from

#define HSPLPrimitive(t) \
instance TermData t where \
  toTerm = Const

-- Primitive types. We can add more of these later.
HSPLPrimitive(())
HSPLPrimitive(Char)
HSPLPrimitive(Bool)
HSPLPrimitive(Int)
HSPLPrimitive(Integer)

-- Types with Generic instances.
instance (TermData a, TermData b) => TermData (a, b)
instance (TermData a, TermData b, TermData c) => TermData (a, b, c)
instance (TermData a, TermData b, TermData c, TermData d) => TermData (a, b, c, d)
instance (TermData a, TermData b, TermData c, TermData d, TermData e) => TermData (a, b, c, d, e)

instance {-# OVERLAPPABLE #-} ( TermData a
                              , Typeable a
                              , Eq a
#ifdef SHOW_TERMS
                              , Show a
#endif
                              ) => TermData [a] where
  toTerm = List . map Const

instance {-# OVERLAPPING #-} ( TermData a
                             , Typeable a
                             , Eq a
#ifdef SHOW_TERMS
                             , Show a
#endif
                             ) => TermData [Variable a] where
  toTerm = List . map Var

instance ( TermData a
         , Typeable a
         , Eq a
#ifdef SHOW_TERMS
         , Show a
#endif
         ) => TermData (Variable a) where
  toTerm = Var

-- | Generic class which allows the conversion of (almost) arbitrary types to 'TermRep's.
class GTermData f where
  gToTerm :: f a -> TermRep

instance GTermData U1 where
  gToTerm _ = Const ()

instance (GTermData f, GTermData g) => GTermData (f :*: g) where
  gToTerm (a :*: b) = Product (gToTerm a) (gToTerm b)

instance (GTermData f, GTermData g) => GTermData (f :+: g) where
  gToTerm (L1 a) = LeftSum $ gToTerm a
  gToTerm (R1 b) = RightSum $ gToTerm b

instance (GTermData f) => GTermData (M1 i c f) where
  gToTerm (M1 a) = gToTerm a

instance (TermData a) => GTermData (K1 i a) where
  gToTerm (K1 a) = toTerm a

-- | A variable is a term which unifies with any other term of the same type. The only purpose of
-- having a 'Variable' representation separate from 'Term' is to annotate variables with a phantom
-- type corresponding to the HSPL type of the variable.
data Variable a where
  Variable :: Typeable a => String -> Variable a
deriving instance Typeable a => Typeable (Variable a)

instance Eq (Variable a) where
  Variable x == Variable y = x == y

instance Show (Variable a) where
  show v@(Variable x) = x ++ " :: " ++ show (varType v)

-- | Determine the HSPL type of a 'Variable'.
varType :: forall a. Typeable a => Variable a -> TypeRep
varType _ = typeOf (undefined :: a)

-- | Smart construct for 'Variable's.
var :: Typeable a => String -> Variable a
var = Variable

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
data TermRep =
            -- | A variable is a term which unifies with any other term.
            forall a. Typeable a => Var (Variable a)
            -- | A constant value of a Haskell data type.
          | forall a. ( Typeable a
                      , Eq a
#ifdef SHOW_TERMS
                      , Show a
#endif
                      ) => Const a
            -- | A product type, such as a tuple of terms.
          | Product TermRep TermRep
            -- | A sum type, such as @Either@.
          | LeftSum TermRep
          | RightSum TermRep
            -- | A destructurable list of terms.
          | List [TermRep]

instance Eq TermRep where
  Var x == Var y = case cast x of
    Just x' -> x' == y
    Nothing -> False

  Const x == Const y = case cast x of
    Just x' -> x' == y
    Nothing -> False

  Product x y == Product x' y' = x == x' && y == y'

  LeftSum x == LeftSum y = x == y
  RightSum x == RightSum y = x == y

  List xs == List ys = all (uncurry (==)) (xs `zip` ys)

  _ == _ = False

instance Show TermRep where
  show (Var x) = show x
#ifdef SHOW_TERMS
  show (Const x) = show x
#else
  show (Const _) = "Const"
#endif
  show (Product x y) = "Tuple (" ++ show x ++ ", " ++ show y ++ ")"
  show (LeftSum x) = "Left (" ++ show x ++ ")"
  show (RightSum y) = "Right (" ++ show y ++ ")"
  show (List xs) = "[" ++ intercalate ", " (map show xs) ++ "]"

-- | A representation of a term and the HSPL type of the represented term.
data Term = Term TermRep TypeRep

instance Show Term where
  show (Term t _) = show t

instance Eq Term where
  (Term t ty) == (Term t' ty') = ty == ty' && t == t'

-- | Smart constructor for building 'Term's out of Haskell constants.
tconst :: ( Typeable a
          , Eq a
#ifdef SHOW_TERMS
          , Show a
#endif
          ) => a -> Term
tconst a = Term (Const a) (typeOf a)

-- | Smart constructor for bulding 'Term's out of 'TermData' instances.
term :: forall a. (TermData a) => a -> Term
term a = Term (toTerm a) (typeOf (undefined :: HSPLType a))

-- | Determine the HSPL type of a 'Term'.
termType :: Term -> TypeRep
termType (Term _ t) = t

-- | A predicate is a truth-valued proposition about 0 or more terms. In this implementation, all
-- predicates are 1-ary -- they each take a single term. This is sufficient because the generic
-- nature of 'TermRep' means that the term could encode a product type such as a tuple, or (). Thus,
-- 0-ary predicates have the form @Predicate "foo" (tconst ())@ and n-ary predicates look like
-- @Predicate "bar" (term (True, 1, "hi"))@.
data Predicate = Predicate String Term
  deriving (Eq)

instance Show Predicate where
  show (Predicate name args) = name ++ "(" ++ show args ++ ")"

-- | Smart constructor for building 'Predicate's out of Haskell types.
predicate :: (TermData a) => String -> a -> Predicate
predicate s a = Predicate s (term a)

-- | Determine the HSPL type of a 'Predicate'.
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
type PredMap = M.Map TypeRep (M.Map String [HornClause])

-- | A program containing no clauses.
emptyProgram :: PredMap
emptyProgram = M.empty

-- | Add a clause to a program.
addClause :: HornClause -> PredMap -> PredMap
addClause c@(HornClause (Predicate name _) _) m =
  let ty = clauseType c
      innerM = M.findWithDefault M.empty ty m
      cs = M.findWithDefault [] name innerM
      innerM' = M.insert name (c : cs) innerM
      m' = M.insert ty innerM' m
  in m'

-- | Syntactic sugar for multiple calls to 'addClause'.
addClauses :: [HornClause] -> PredMap -> PredMap
addClauses cs m = m'
  where (_, m') = runState comp m
        comp = forM cs $ \c -> modify $ addClause c

-- | Return all 'HornClause's which have the same name and type as the given 'Predicate'.
findClauses :: Predicate -> PredMap -> [HornClause]
findClauses p@(Predicate name _) m =
  let ty = predType p
      innerM = M.findWithDefault M.empty ty m
      cs = M.findWithDefault [] name innerM
  in cs
