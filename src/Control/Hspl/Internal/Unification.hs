{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.Unification
Description : Functions supporting the unification of terms, predicates, and clauses.
Stability   : Internal

This module defines a framework for predicate logic unification. It provides functions to determine
unifiying substitutions for a pair of terms and to apply those substitutions to other terms and
predicates. It also allows for the renaming of variables within a clause to preserve the meaning of
the clause while ensuring that it shares no free variabels with another clause. This process is
necessary before unifying to clauses.
-}
module Control.Hspl.Internal.Unification (
  -- * Unifiers
    SubMap (..)
  , Unifier (..)
  -- ** Operations on unifiers
  , updateSubMap
  , compose
  , (//)
  -- ** Querying a unifier
  , UnificationStatus (..)
  , findVar
  , findVarWithDefault
  , queryVar
  , isSubunifierOf
  -- * Unification
  -- ** Auxiliary functions
  , freeIn
  , mgu
  , unifyTerm
  , unifyPredicate
  , unifyGoal
  , unify
  -- ** The unification monad
  , UnificationT
  , Unification
  , runUnification
  , runUnificationT
  , unifyClause
  -- * Renaming
  , VarMap (..)
  , Renamer (..)
  , RenamedT
  , Renamed
  , renameVar
  , renameTerm
  , renamePredicate
  , renameGoal
  , renameClause
  ) where

import           Control.Exception
import           Control.Monad.Identity
import           Control.Monad.State
import           Data.List
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid hiding (Sum, Product)
import           Data.Typeable

import Control.Hspl.Internal.Ast

-- | A type-erased wrapper for a map from variables of a particular type to the terms replacing
-- those variables. We will use this to build a generalized 'Unifier' supporting variables of any
-- type. However, this intermediate structure allows the compiler to prove that a variable will
-- never map to a term of the wrong type, a nice property to have.
data SubMap = forall a. Typeable a => SubMap (M.Map (Var a) (Term a))

instance Eq SubMap where
  (==) (SubMap m) (SubMap m') = case cast m' of
    Just m'' -> m == m''
    Nothing -> False

instance Show SubMap where
  show (SubMap m) = intercalate ", " (map showSubstitution $ M.toList m)
    where showSubstitution (x, t) = "(" ++ show t ++ ") / (" ++ show x ++ ")"

-- | The generalized unifier type. Conceptually, a unifier maps variables to terms which are to
-- replace those variables. In this implementation, we use a multi-level mapping: this type maps
-- the /type of a variable/ to the 'SubMap' for that type, which in term maps the name of the
-- variable to its replacement.
newtype Unifier = Unifier { unUnifier :: M.Map TypeRep SubMap }
  deriving (Eq)

instance Show Unifier where
  show (Unifier m) = "[" ++ intercalate ", " (map show $ M.elems m) ++ "]"

instance Monoid Unifier where
  mempty = Unifier M.empty
  mappend = compose

-- | Find the term which is to replace a given variable. If no variable of the right name /and/ type
-- exists in the 'Unifier', this returns 'Nothing'.
findVar :: Typeable a => Unifier -> Var a -> Maybe (Term a)
findVar (Unifier u) x = do
  SubMap u' <- M.lookup (varType x) u
  u'' <- cast u'
  M.lookup x u''

-- | Convenience function to get either the replacement for a variable or some default value if the
-- variable is not found.
findVarWithDefault :: Typeable a => Term a -> Unifier -> Var a -> Term a
findVarWithDefault t u x = fromMaybe t $ findVar u x

-- | Update the substitutions described by a 'SubMap' after further unification has taken place. For
-- each variable in the 'Unifier', every free ocurrence of that variable in a 'Term' in the 'SubMap'
-- is replaced by the corresponding 'Term' from the 'Unifier'. Then, all substitutions of the right
-- type which are present in the 'Unifier' but not in the 'SubMap' are added to the 'SubMap'.
updateSubMap :: Unifier -> SubMap -> SubMap
updateSubMap u (SubMap m) =
  let
    -- Apply the second unifier to the substitutions in the first
    m' = M.map (unifyTerm u) m

    -- Find the corresponding submap in u
    (x, _) = M.elemAt 0 m'
    ty = varType x
    m2 = do
      SubMap m2Untyped <- M.lookup ty (unUnifier u)
      cast m2Untyped

  -- Return the left-biased union of the two maps
  in case m2 of
    Just m2' -> SubMap $ M.union m' m2'
    Nothing -> SubMap m'

-- | Compute the composition of two 'Unifier's. This is the net unification that results from
-- applying the first unifier and then the second in sequence.
compose :: Unifier -> Unifier -> Unifier
compose (Unifier u1) gu2@(Unifier u2) =
  let u1' = M.map (updateSubMap gu2) u1
  in Unifier $ M.union u1' u2

-- | A unifier representing the replacement of a variable by a term.
(//) :: TermData a => a -> Var (HSPLType a) -> Unifier
t // x = Unifier $ M.singleton (varType x) $ SubMap (M.singleton x (toTerm t))

-- | @u1 `isSubunifierOf` u2@ if and only if every substitution in @u1@ is also in @u2@.
isSubunifierOf :: Unifier -> Unifier -> Bool
isSubunifierOf (Unifier u1) (Unifier u2) = all isSubSubmap $ M.toList u1
  where isSubSubmap (ty, SubMap m1) = case M.lookup ty u2 >>= \(SubMap m2) -> cast m2 of
                                        Just m2' -> m1 `M.isSubmapOf` m2'
                                        Nothing -> False

-- | Determine if the variable x is free in the term t. This is useful, for example, when performing
-- the occurs check before computing a 'Unifier'.
freeIn :: (Typeable a, Typeable b) => Var a -> Term b -> Bool
freeIn x (Variable y) = case cast y of
  Just y' -> x == y'
  Nothing -> False
freeIn _ (Constant _) = False
freeIn x (Constructor _ t) = freeIn x t
freeIn x (Tup t ts) = freeIn x t || freeIn x ts
freeIn x (List t ts) = freeIn x t || freeIn x ts
freeIn _ Nil = False
freeIn x (Sum t1 t2) = freeIn x t1 || freeIn x t2
freeIn x (Difference t1 t2) = freeIn x t1 || freeIn x t2
freeIn x (Product t1 t2) = freeIn x t1 || freeIn x t2
freeIn x (Quotient t1 t2) = freeIn x t1 || freeIn x t2
freeIn x (IntQuotient t1 t2) = freeIn x t1 || freeIn x t2
freeIn x (Modulus t1 t2) = freeIn x t1 || freeIn x t2

-- | Compute the most general unifier for two 'Term's. A "most general unifier" is a 'Unifier' that
-- cannot be created by composing (@<>@) two smaller unifiers. This function will fail with
-- 'Nothing' if the two terms cannot be unified.
mgu :: Term a -> Term a -> Maybe Unifier
mgu (Variable x) (Variable y)
  | x == y = Just mempty -- no occurs check if we're unifying to variables
  | otherwise = case y of
    -- When one variable is a program-generated 'Fresh' variable, prefer to replace it with the
    -- other, thereby keeping user-defined variables in play as long as possible. Semantically it
    -- makes no difference, but user-defined variables mean something to the client whereas 'Fresh'
    -- variables do not; therefore, keeping the user-defined variables may make HSPL programs easier
    -- to inspect, debug, and reason about.
    Fresh _ -> Just $ toTerm x // y
    _ -> Just $ toTerm y // x
mgu (Variable x) t
  | freeIn x t = Nothing -- occurs check
  | otherwise = Just $ t // x
mgu t (Variable x)
  | freeIn x t = Nothing -- occurs check
  | otherwise = Just $ t // x

mgu (Constant c) (Constant c')
  | c == c' = Just mempty
  | otherwise = Nothing

mgu (Constructor f t) (Constructor f' t') = case cast t' of
  Just t'' -> if constructor f == constructor f' then mgu t t'' else Nothing
  Nothing -> Nothing

mgu (Tup t ts) (Tup t' ts') = mguBinaryTerm (t, ts) (t', ts')

mgu Nil Nil = Just mempty
mgu (List _ _) Nil = Nothing
mgu Nil (List _ _) = Nothing
mgu (List t ts) (List t' ts') = mguBinaryTerm (t, ts) (t', ts')

mgu (Sum t1 t2) (Sum t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
mgu (Difference t1 t2) (Difference t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
mgu (Product t1 t2) (Product t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
mgu (Quotient t1 t2) (Quotient t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
mgu (IntQuotient t1 t2) (IntQuotient t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
mgu (Modulus t1 t2) (Modulus t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')

mgu _ _ = Nothing

-- | Helper function for computing the 'mgu' of a 'Term' with two subterms.
mguBinaryTerm :: (Term a, Term b) -> (Term a, Term b) -> Maybe Unifier
mguBinaryTerm (t1, t2) (t1', t2') = do
  -- Unify the subterms in sequence, applying each intermediate unifier to the remaining terms
  mgu1 <- mgu t1 t1'
  let ut2 = unifyTerm mgu1 t2
  let ut2' = unifyTerm mgu1 t2'
  mgu2 <- mgu ut2 ut2'
  return $ mgu1 <> mgu2

-- | Apply a 'Unifier' to a 'Term' and return the new 'Term', in which all free variables appearing
-- in the unifier are replaced by the corresponding sub-terms.
unifyTerm :: Unifier -> Term a -> Term a
unifyTerm u v@(Variable x) = findVarWithDefault v u x
unifyTerm _ c@(Constant _) = c
unifyTerm u (Constructor f t) = Constructor f (unifyTerm u t)
unifyTerm u (Tup t ts) = Tup (unifyTerm u t) (unifyTerm u ts)
unifyTerm u (List t ts) = List (unifyTerm u t) (unifyTerm u ts)
unifyTerm _ Nil = Nil
unifyTerm u (Sum t1 t2) = Sum (unifyTerm u t1) (unifyTerm u t2)
unifyTerm u (Difference t1 t2) = Difference (unifyTerm u t1) (unifyTerm u t2)
unifyTerm u (Product t1 t2) = Product (unifyTerm u t1) (unifyTerm u t2)
unifyTerm u (Quotient t1 t2) = Quotient (unifyTerm u t1) (unifyTerm u t2)
unifyTerm u (IntQuotient t1 t2) = IntQuotient (unifyTerm u t1) (unifyTerm u t2)
unifyTerm u (Modulus t1 t2) = Modulus (unifyTerm u t1) (unifyTerm u t2)

-- | Apply a 'Unifier' to the argument of a 'Predicate'.
unifyPredicate :: Unifier -> Predicate -> Predicate
unifyPredicate u (Predicate name term) = Predicate name (unifyTerm u term)

-- | Apply a 'Unifier' to a 'Goal'.
unifyGoal :: Unifier -> Goal -> Goal
unifyGoal u (PredGoal p) = PredGoal $ unifyPredicate u p
unifyGoal u (CanUnify t1 t2) = CanUnify (unifyTerm u t1) (unifyTerm u t2)
unifyGoal u (Identical t1 t2) = Identical (unifyTerm u t1) (unifyTerm u t2)
unifyGoal u (Not g) = Not $ unifyGoal u g
unifyGoal u (Equal t1 t2) = Equal (unifyTerm u t1) (unifyTerm u t2)

-- | Apply a 'Unifier' to all 'Predicate's in a 'HornClause'.
unifyClause :: Unifier -> HornClause -> HornClause
unifyClause u (HornClause p n) = HornClause (unifyPredicate u p) (map (unifyGoal u) n)

-- | Unify a 'Predicate' with a 'HornClause' with a matching positive literal. Assuming the
-- predicate unifies with the positive literal of the clause, the 'mgu' is applied to each negative
-- literal and the resulting disjunction is returned. Before unification, the 'HornClause' is
-- renamed apart so that it does not share any free variables with the goal.
unify :: Monad m => Predicate -> HornClause -> UnificationT m (Maybe ([Goal], Unifier))
unify (Predicate name arg) c@(HornClause (Predicate name' _) _) =
  assert (name == name') $ do
    HornClause (Predicate _ arg') negs <- renameClause c
    case cast arg' >>= mgu arg of
      Nothing -> return Nothing
      Just u -> return $ Just (map (unifyGoal u) negs, u)

-- | The status of a variable in a given 'Unifier'. At any given time, a variable occupies a state
-- represented by one of the constructors.
data UnificationStatus a =
    -- | The variable has unified with a 'Term' containing no free variables. The Haskell value
    -- corresponding to that term can thus be reconstructed in full.
    Unified a
    -- | The variable has unified with a 'Term', but that term contains free variables and thus the
    -- corresponding Haskell value cannot be reconstructed without further unification.
  | Partial (Term a)
    -- | The variable has not been unified (no mapping from this variable to any term exists in the
    -- 'Unifier').
  | Ununified
  deriving (Show, Eq)

-- | Query the unification status of a variable.
queryVar :: Typeable a => Unifier -> Var a -> UnificationStatus a
queryVar u x = case findVar u x of
  Nothing -> Ununified
  Just t -> case fromTerm t of
    Nothing -> Partial t
    Just c -> Unified c

-- | A type-erased wrapper for a map from variables to the variable the should be replaced with upon
-- renaming.
data VarMap = forall a. Typeable a => VarMap (M.Map (Var a) (Var a))
deriving instance Show VarMap

instance Eq VarMap where
  (==) (VarMap m) (VarMap m') = case cast m' of
    Just m'' -> m == m''
    Nothing -> False

-- | A wrapper around 'VarMap' which contains the renamings for variables of all types.
data Renamer = Renamer (M.Map TypeRep VarMap)
  deriving (Show, Eq)

-- | Monad encapsulating the state of a renaming operation.
type RenamedT m = StateT Renamer (UnificationT m)

-- | Non-transformed version of the 'RenamedT' monad.
type Renamed = RenamedT Identity

-- | Monad in which all unification operations take place. This type encapsulates the state
-- necessary to generate unique 'Fresh' variables. All unifications in a single run of an HSPL
-- program should take place in the same 'UnificationT' monad.
type UnificationT = StateT Int

-- | Non-transformer version of the 'UnificationT' monad.
type Unification = UnificationT Identity

-- | Evaluate a computation in the 'Unification' monad, starting from a state in which no 'Fresh'
-- variables have been generated.
runUnification :: Unification a -> a
runUnification m = evalState m 0

-- | Evaluate a computation in 'UnificationT' transformed monad, starting from a state in which no
-- 'Fresh' variables have been generated. The result is a compuation in the underlying monad.
runUnificationT :: Monad m => UnificationT m a -> m a
runUnificationT m = evalStateT m 0

-- | Replace a variable with a new, unique name. If this variable appears in the current 'Renamer',
-- it is replaced with the corresonding new name. Otherwise, a 'Fresh' variable with a unique ID is
-- generated and added to the 'Renamer'.
renameVar :: (Typeable a, Monad m) => Var a -> RenamedT m (Var a)
renameVar x = do
  fresh <- lift get
  Renamer m <- get
  let freshX = Fresh fresh
  case M.lookup (varType x) m of
    Nothing ->
      let m' = M.insert (varType x) (VarMap $ M.singleton x freshX) m
      in put (Renamer m') >> lift (put (fresh + 1)) >> return freshX
    Just (VarMap untypedVarMap) -> case cast untypedVarMap of
      Nothing -> error $ "Found VarMap of incorrect type (" ++ show (typeOf untypedVarMap) ++ ") " ++
                 "with key of type " ++ show (varType x)
      Just m' -> case M.lookup x m' of
        Nothing ->
          let m'' = VarMap $ M.insert x freshX m'
          in put (Renamer (M.insert (varType x) m'' m)) >> lift (put (fresh + 1)) >> return freshX
        Just x' -> return x'

-- | Rename all of the variables in a term.
renameTerm :: Monad m => Term a -> RenamedT m (Term a)
renameTerm (Variable x) = liftM Variable $ renameVar x
renameTerm (Constant c) = return $ Constant c
renameTerm (Tup t ts) = renameBinaryTerm Tup t ts
renameTerm (List t ts) = renameBinaryTerm List t ts
renameTerm Nil = return Nil
renameTerm (Constructor f t) = liftM (Constructor f) $ renameTerm t
renameTerm (Sum t1 t2) = renameBinaryTerm Sum t1 t2
renameTerm (Difference t1 t2) = renameBinaryTerm Difference t1 t2
renameTerm (Product t1 t2) = renameBinaryTerm Product t1 t2
renameTerm (Quotient t1 t2) = renameBinaryTerm Quotient t1 t2
renameTerm (IntQuotient t1 t2) = renameBinaryTerm IntQuotient t1 t2
renameTerm (Modulus t1 t2) = renameBinaryTerm Modulus t1 t2

-- | Helper function for renaming variables in a 'Term' with two subterms.
renameBinaryTerm :: Monad m =>
                    (Term a -> Term b -> Term c) -> Term a -> Term b -> RenamedT m (Term c)
renameBinaryTerm constr t1 t2 = do
  rt1 <- renameTerm t1
  rt2 <- renameTerm t2
  return $ constr rt1 rt2

-- | Rename all of the variables in a predicate.
renamePredicate :: Monad m => Predicate -> RenamedT m Predicate
renamePredicate (Predicate name arg) = liftM (Predicate name) $ renameTerm arg

-- | Rename all of the variables in a goal.
renameGoal :: Monad m => Goal -> RenamedT m Goal
renameGoal (PredGoal p) = liftM PredGoal $ renamePredicate p
renameGoal (CanUnify t1 t2) = renameBinaryGoal CanUnify t1 t2
renameGoal (Identical t1 t2) = renameBinaryGoal Identical t1 t2
renameGoal (Not g) = liftM Not $ renameGoal g
renameGoal (Equal t1 t2) = renameBinaryGoal Equal t1 t2

-- | Helper function for renaming variables in a 'Goal' with two 'Term' arguments.
renameBinaryGoal :: Monad m => (Term a -> Term b -> Goal) -> Term a -> Term b -> RenamedT m Goal
renameBinaryGoal constr t1 t2 = do
  t1' <- renameTerm t1
  t2' <- renameTerm t2
  return $ constr t1' t2'

-- | Rename all of the variables in a clause.
renameClause :: Monad m => HornClause -> UnificationT m HornClause
renameClause (HornClause p n) = evalStateT rename (Renamer M.empty)
  where rename = do rp <- renamePredicate p
                    rn <- forM n renameGoal
                    return $ HornClause rp rn
