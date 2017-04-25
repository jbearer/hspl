{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
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
  --
  -- ** Mappings from Haskell types to HSPL types
  --
  -- $typeMappings
    ResolveVariables
  , GResolveVariables
  -- ** Conversions from Haskell types to HSPL types
  , TermData (..)
  , GTermData (..)
  -- * AST
  , Variable (..)
  , Term (..)
  , Predicate (..)
  , HornClause (..)
  , PredMap
  -- * Functions for building a program
  , predicate
  , emptyProgram
  , addClause
  , addClauses
  -- * Functions for inspecting a program
  , varType
  , predType
  , clauseType
  , findClauses
  , fromTerm
  ) where

import           Control.Monad.State
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

{- $typeMappings
The purpose of these type families is to provide a level of indirection between Haskell types and
HSPL types. For most types, these are the same. However, for HSPL variables, the HSPL type of the
Haskell type @Variable a@ is @a@ (the type contained by the variable). These families also provide
instances for destructuring compound types such as tuples, which allows the embedding of variables
within tuples.
-}

-- | Map from Haskell types to HSPL types. This map sends types of the form @Variable a@ to @a@, and
-- does so recursively for recursively defined data types. Otherwise, it sends @a@ to itself.
type family ResolveVariables a where
  ResolveVariables (Variable a) = ResolveVariables a
  ResolveVariables (a, b) = (ResolveVariables a, ResolveVariables b)
  ResolveVariables [a] = [ResolveVariables a]
  ResolveVariables a = a

-- | Generic version of 'ResolveVariables'. Sends a representation of a Haskell type to a
-- representation of the corresponding HSPL type. This map should satisfy the property
--
-- prop> GResolveVariables (Rep a) = Rep (ResolveVariables a)
--
-- for all types @a@ with an instance for 'Generic'.
type family GResolveVariables (f :: * -> *) :: * -> * where
  GResolveVariables U1 = U1
  GResolveVariables (K1 i c) = K1 i (ResolveVariables c)
  GResolveVariables (M1 i c f) = M1 i c (GResolveVariables f)
  GResolveVariables (f :+: g) = GResolveVariables f :+: GResolveVariables g
  GResolveVariables (f :*: g) = GResolveVariables f :*: GResolveVariables g

class (Generic a, a ~ ResolveVariables a, Rep a ~ GResolveVariables (Rep a)) => NoVariables a where {}
instance (Generic a, a ~ ResolveVariables a, Rep a ~ GResolveVariables (Rep a)) => NoVariables a

class (Generic a, Rep (ResolveVariables a) ~ GResolveVariables (Rep a)) => NotAVariable a where {}
instance (Generic a, Rep (ResolveVariables a) ~ GResolveVariables (Rep a)) => NotAVariable a

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
class (Generic (ResolveVariables a)) => TermData a where
  toTerm :: a -> Term (Rep (ResolveVariables a))

  default toTerm :: (NotAVariable a, GTermData (Rep a)) => a -> Term (GResolveVariables (Rep a))
  toTerm = gToTerm . from

instance (Typeable a, NoVariables a) => TermData (Variable a) where
  toTerm = Var

instance TermData Bool where
  toTerm = Const

deriving instance Generic Char
instance TermData Char where
  toTerm = Const

instance TermData () where
  toTerm = Const

deriving instance Generic Int
instance TermData Int where
  toTerm = Const

instance TermData a => TermData [a]
instance (TermData a, TermData b) => TermData (a, b)

-- | Generic version of 'TermData'. Converts an instantiation of @Rep a@ to a 'Term' abstraction.
class GTermData f where
  gToTerm :: f a -> Term (GResolveVariables f)

instance GTermData U1 where
  gToTerm U1 = Unit

instance (TermData c) => GTermData (K1 i c) where
  gToTerm (K1 c) = SubTerm $ toTerm c

instance (GTermData f, Datatype c) => GTermData (D1 c f) where
  gToTerm (M1 t) = MData $ gToTerm t

instance (GTermData f, Constructor c) => GTermData (C1 c f) where
  gToTerm (M1 t) = MCon $ gToTerm t

instance (GTermData f, Selector c) => GTermData (S1 c f) where
  gToTerm (M1 t) = MSel $ gToTerm t

instance (GTermData f, GTermData g) => GTermData (f :+: g) where
  gToTerm (L1 t) = LeftSum $ gToTerm t
  gToTerm (R1 t) = RightSum $ gToTerm t

instance (GTermData f, GTermData g) => GTermData (f :*: g) where
  gToTerm (t1 :*: t2) = Product (gToTerm t1) (gToTerm t2)

-- | A variable is a term which unifies with any other term of the same type. The only purpose of
-- having a 'Variable' representation separate from 'Term' is to annotate variables with a phantom
-- type corresponding to the HSPL type of the variable.
data Variable a where
  Variable :: Typeable a => String -> Variable a
  deriving (Typeable)

deriving instance Eq (Variable a)

instance Show (Variable a) where
  show v@(Variable x) = x ++ " :: " ++ show (varType v)

-- | Determine the HSPL type of a 'Variable'.
varType :: forall a. Variable a -> TypeRep
varType (Variable _) = typeOf (undefined :: a)

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
data Term (f :: * -> *) where
  Unit :: Term U1
  Const :: ( Typeable c
           , Generic c
           , Eq c
#ifdef SHOW_TERMS
           , Show c
#endif
           ) => c -> Term (Rep c)
  SubTerm :: Generic c => Term (Rep c) -> Term (K1 i c)
  MData :: Datatype c => Term f -> Term (D1 c f)
  MCon :: Constructor c => Term f -> Term (C1 c f)
  MSel :: Selector c => Term f -> Term (S1 c f)
  Product :: Term f -> Term g -> Term (f :*: g)
  LeftSum :: Term f -> Term (f :+: g)
  RightSum :: Term g -> Term (f :+: g)
  Var :: Typeable a => Variable a -> Term (Rep a)
  deriving (Typeable)

instance Eq (Term f) where
  Unit == Unit = True
  Const c == Const c' = case cast c' of
    Just c'' -> c == c''
    Nothing -> False
  SubTerm t == SubTerm t' = t == t'
  MData t == MData t' = t == t'
  MCon t == MCon t' = t == t'
  MSel t == MSel t' = t == t'
  Product t u == Product t' u' = t == t' && u == u'
  LeftSum t == LeftSum t' = t == t'
  RightSum t == RightSum t' = t == t'
  Var x == Var x' = case cast x' of
    Just x'' -> x == x''
    Nothing -> False
  _ == _ = False

instance Show (Term f) where
  show Unit = ""
#ifdef SHOW_TERMS
  show (Const c) = show c
#else
  show (Const _) = "<const>"
#endif
  show (SubTerm t) = show t
  show (MData t) = show t
  show (MCon t) = conName (undefined :: f ()) ++ " (" ++ show t ++ ")"
  show (MSel t) = "{" ++ selName (undefined :: f ()) ++ " = " ++ show t ++ "}"
  show (Product t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (LeftSum t) = "L1 (" ++ show t ++ ")"
  show (RightSum t) = "R1 (" ++ show t ++ ")"
  show (Var v) = show v

-- | Convert an HSPL 'Term' back into the Haskell value which it represents, if possible. If the
-- 'Term' contains any 'Variable's, this will fail with 'Nothing'. Otherwise, it will return the
-- Haskell value. This function satisfies the property that for all @t :: a@ such that @t@ contains
-- no variables and @a@ has an instance for 'TermData',
--
-- prop> fromTerm $ toTerm t = Just t
fromTerm :: Generic a => Term (Rep a) -> Maybe a
fromTerm term = to <$> unTerm term
  where unTerm :: Term f -> Maybe (f a)
        unTerm Unit = Just U1
        unTerm (Const c) = Just $ from c
        unTerm (SubTerm t) = K1 <$> fromTerm t
        unTerm (MData t) = M1 <$> unTerm t
        unTerm (MCon t) = M1 <$> unTerm t
        unTerm (MSel t) = M1 <$> unTerm t
        unTerm (Product t1 t2) = do
          ut1 <- unTerm t1
          ut2 <- unTerm t2
          return $ ut1 :*: ut2
        unTerm (LeftSum t) = L1 <$> unTerm t
        unTerm (RightSum t) = R1 <$> unTerm t
        unTerm (Var _) = Nothing

-- | A predicate is a truth-valued proposition about 0 or more terms. In this implementation, all
-- predicates are 1-ary -- they each take a single term. This is sufficient because the generic
-- nature of 'TermRep' means that the term could encode a product type such as a tuple, or (). Thus,
-- 0-ary predicates have the form @Predicate "foo" (tconst ())@ and n-ary predicates look like
-- @Predicate "bar" (term (True, 1, "hi"))@.
data Predicate = forall f. Typeable f => Predicate String (Term f)

instance Show Predicate where
  show (Predicate name args) = name ++ "(" ++ show args ++ ")"

instance Eq Predicate where
  Predicate p t == Predicate p' t' = case cast t' of
    Just t'' -> p == p' && t == t''
    Nothing -> False

-- | Smart constructor for building 'Predicate's out of Haskell types.
predicate :: (TermData a, Typeable (Rep (ResolveVariables a))) => String -> a -> Predicate
predicate s a = Predicate s (toTerm a)

-- | Determine the HSPL type of a 'Predicate'. By definition, the type of a 'Predicate' is the type
-- of the 'Term' to which it is applied. For portability reasons, the type of a 'Term' containing
-- a value of a particular type is not a specified part of this module's interface. Therefore,
-- the result of @predType@ should be treated as an opaque structure that can be compared but not
-- inspected.
predType :: Predicate -> TypeRep
predType (Predicate _ t) = typeOf t

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
