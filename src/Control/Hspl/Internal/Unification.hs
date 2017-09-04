{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
    Unifier
  -- ** Operations on unifiers
  , compose
  , (//)
  -- ** Querying a unifier
  , UnificationStatus (..)
  , queryVar
  , isSubunifierOf
  -- * Unification
  -- ** The unification monad
  , MonadUnification (..)
  , UnificationT
  , runUnificationT
  , Unification
  , runUnification
  -- ** Unification algorithm
  , freeIn
  , mgu
  , unifyTerm
  , unifyPredicate
  , unifyGoal
  , unify
  , unifyClause
  -- * Renaming
  , Renamer
  , RenamedT
  , runRenamedT
  , Renamed
  , runRenamed
  , renameVar
  , renameTerm
  , renamePredicate
  , renameGoal
  , renameClause
  ) where

import Control.Applicative (Applicative)
import Control.Exception
import Control.Monad.Identity
import Control.Monad.State
import Data.Typeable

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.VarMap (VarMap)
import qualified Control.Hspl.Internal.VarMap as M

-- | Monad in which all unification operations take place. All unifications in a single run of an
-- HSPL program should take place in the same 'UnificationT' monad.
class Monad m => MonadUnification m where
  -- | Get a 'Fresh' variable.
  fresh :: TermEntry a => m (Var a)

-- | Concrete instance of the 'MonadUnification' class. This type encapsulates the state necessary
-- to generate unique 'Fresh' variables.
newtype UnificationT m a = UnificationT { unUnificationT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)
deriving instance Monad m => MonadState Int (UnificationT m)

instance Monad m => MonadUnification (UnificationT m) where
  fresh = do
    n <- get
    put $ n + 1
    return $ Fresh n

-- | Non-transformer version of the 'UnificationT' monad.
type Unification = UnificationT Identity

-- | Evaluate a computation in the 'Unification' monad, starting from a state in which no 'Fresh'
-- variables have been generated.
runUnification :: Unification a -> a
runUnification = runIdentity . runUnificationT

-- | Evaluate a computation in 'UnificationT' transformed monad, starting from a state in which no
-- 'Fresh' variables have been generated. The result is a compuation in the underlying monad.
runUnificationT :: Monad m => UnificationT m a -> m a
runUnificationT m = evalStateT (unUnificationT m) 0

-- | A unifier maps variables to terms which are to replace those variables.
type Unifier = VarMap Term

-- | Compute the composition of two 'Unifier's. This is the net unification that results from
-- applying the first unifier and then the second in sequence.
infixr 6 `compose` -- Same as <> for Monoid
compose :: Unifier -> Unifier -> Unifier
compose u1 u2 = M.map (unifyTerm u2) u1 `M.union` u2

-- | A unifier representing the replacement of a variable by a term.
(//) :: TermData a => a -> Var (HSPLType a) -> Unifier
t // x = M.singleton x (toTerm t)

-- | @u1 `isSubunifierOf` u2@ if and only if every substitution in @u1@ is also in @u2@.
isSubunifierOf :: Unifier -> Unifier -> Bool
isSubunifierOf u1 u2 = and $ M.collect (\k v -> M.containsMapping k v u2) u1

-- | Determine if the variable x is free in the term t. This is useful, for example, when performing
-- the occurs check before computing a 'Unifier'.
freeIn :: (TermEntry a, TermEntry b) => Var a -> Term b -> Bool
freeIn x (Variable y) = maybe False (==x) $ cast y
freeIn _ (Constant _) = False
freeIn x (Constructor _ t) = any (termMap $ freeIn x) t
freeIn var (Tup tup) = freeInTuple var tup
  where freeInTuple :: (TermEntry a, TermEntry b) => Var a -> TupleTerm b -> Bool
        freeInTuple x (Tuple2 t1 t2) = freeIn x t1 || freeIn x t2
        freeInTuple x (TupleN t ts) = freeIn x t || freeInTuple x ts
freeIn var (List l) = freeInList var l
  where freeInList :: (TermEntry a, TermEntry b) => Var a -> ListTerm b -> Bool
        freeInList x (Cons t ts) = freeIn x t || freeInList x ts
        freeInList x (VarCons t y) = freeIn x t || freeIn x (Variable y)
        freeInList _ Nil = False
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
  | x == y = Just M.empty -- no occurs check if we're unifying to variables
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
  | c == c' = Just M.empty
  | otherwise = Nothing

mgu (Constructor c arg) (Constructor c' arg')
  | c == c' = mguETermList arg arg'
  | otherwise = Nothing
  where mguETermList :: [ErasedTerm] -> [ErasedTerm] -> Maybe Unifier
        mguETermList [] [] = Just M.empty
        mguETermList [] _ = Nothing
        mguETermList _ [] = Nothing
        mguETermList (ETerm t : ts) (ETerm t' : ts') = do u <- cast t' >>= mgu t
                                                          let uts = map (termMap $ ETerm . unifyTerm u) ts
                                                          let uts' = map (termMap $ ETerm . unifyTerm u) ts'
                                                          u' <- mguETermList uts uts'
                                                          return $ u `compose` u'

mgu (Tup tup) (Tup tup') = mguTup tup tup'
  where mguTup :: TermEntry a => TupleTerm a -> TupleTerm a -> Maybe Unifier
        mguTup (Tuple2 t1 t2) (Tuple2 t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
        mguTup (TupleN t ts) (TupleN t' ts') = do u <- mgu t t'
                                                  let uts = unifyTuple u ts
                                                  let uts' = unifyTuple u ts'
                                                  u' <- mguTup uts uts'
                                                  return $ u `compose` u'
        mguTup _ _ = Nothing

mgu (List l) (List l') = mguList l l'
  where mguList :: ListTerm a -> ListTerm a -> Maybe Unifier
        mguList Nil Nil = Just M.empty
        mguList (Cons t ts) (Cons t' ts') = mguBinaryTerm (t, List ts) (t', List ts')
        mguList (VarCons t x) (VarCons t' x') = mguBinaryTerm (t, Variable x) (t', Variable x')
        mguList (VarCons t x) (Cons t' ts) = mguBinaryTerm (t, Variable x) (t', List ts)
        mguList (Cons t ts) (VarCons t' x) = mguBinaryTerm (t, List ts) (t', Variable x)
        mguList _ _ = Nothing

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
  return $ mgu1 `compose` mgu2

unifyTuple :: Unifier -> TupleTerm a -> TupleTerm a
unifyTuple u (Tuple2 t1 t2) = Tuple2 (unifyTerm u t1) (unifyTerm u t2)
unifyTuple u (TupleN t ts) = TupleN (unifyTerm u t) (unifyTuple u ts)

-- | Apply a 'Unifier' to a 'Term' and return the new 'Term', in which all free variables appearing
-- in the unifier are replaced by the corresponding sub-terms.
unifyTerm :: Unifier -> Term a -> Term a
unifyTerm u v@(Variable x) = M.findWithDefault v x u
unifyTerm _ c@(Constant _) = c
unifyTerm u (Constructor c ts) = Constructor c $ map (termMap $ ETerm . unifyTerm u) ts
unifyTerm u (Tup t) = Tup $ unifyTuple u t
unifyTerm unifier (List l) = List $ unifyList unifier l
  where unifyList :: Unifier -> ListTerm a -> ListTerm a
        unifyList u (Cons t ts) = Cons (unifyTerm u t) (unifyList u ts)
        unifyList u (VarCons t x) =
          case getListTerm $ unifyTerm u $ Variable x of
            Left ux -> VarCons (unifyTerm u t) ux
            Right xs -> Cons (unifyTerm u t) xs
        unifyList _ Nil = Nil
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
unifyGoal u (PredGoal p cs) = PredGoal (unifyPredicate u p) cs
unifyGoal u (CanUnify t1 t2) = CanUnify (unifyTerm u t1) (unifyTerm u t2)
unifyGoal u (Identical t1 t2) = Identical (unifyTerm u t1) (unifyTerm u t2)
unifyGoal u (Equal t1 t2) = Equal (unifyTerm u t1) (unifyTerm u t2)
unifyGoal u (LessThan t1 t2) = LessThan (unifyTerm u t1) (unifyTerm u t2)
unifyGoal u (Not g) = Not $ unifyGoal u g
unifyGoal u (And g1 g2) = And (unifyGoal u g1) (unifyGoal u g2)
unifyGoal u (Or g1 g2) = Or (unifyGoal u g1) (unifyGoal u g2)
unifyGoal _ Top = Top
unifyGoal _ Bottom = Bottom
unifyGoal u (Alternatives x g xs) = Alternatives (unifyTerm u x) (unifyGoal u g) (unifyTerm u xs)
unifyGoal u (Once g) = Once $ unifyGoal u g
unifyGoal _ Cut = Cut

-- | Apply a 'Unifier' to all 'Predicate's in a 'HornClause'.
unifyClause :: Unifier -> HornClause -> HornClause
unifyClause u (HornClause p n) = HornClause (unifyPredicate u p) (unifyGoal u n)

-- | Unify a 'Predicate' with a 'HornClause' with a matching positive literal. Assuming the
-- predicate unifies with the positive literal of the clause, the 'mgu' is applied to the negative
-- literal and the resulting goal is returned. Before unification, the 'HornClause' is renamed apart
-- so that it does not share any free variables with the goal.
unify :: MonadUnification m => Predicate -> HornClause -> m (Maybe (Goal, Unifier))
unify (Predicate name arg) c@(HornClause (Predicate name' _) _) =
  assert (name == name') $ do
    HornClause (Predicate _ arg') neg <- renameClause c
    case cast arg' >>= mgu arg of
      Nothing -> return Nothing
      Just u -> return $ Just (unifyGoal u neg, u)

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
queryVar :: TermEntry a => Unifier -> Var a -> UnificationStatus a
queryVar u x = case M.lookup x u of
  Nothing -> Ununified
  Just t -> case fromTerm t of
    Nothing -> Partial t
    Just c -> Unified c

-- | A renamer maps variables to 'Fresh' variables with which the former should be renamed.
type Renamer = VarMap Var

-- | Monad encapsulating the state of a renaming operation.
type RenamedT m = StateT Renamer m

-- | Non-transformed version of the 'RenamedT' monad.
type Renamed = RenamedT Unification

-- | Evaluate a computation in a 'RenamedT' monad.
runRenamedT :: MonadUnification m => RenamedT m a -> m a
runRenamedT m = evalStateT m M.empty

-- | Special case of 'runRenamedT' for the plain 'Renamed' monad.
runRenamed :: Renamed a -> a
runRenamed = runUnification . runRenamedT

-- | Replace a variable with a new, unique name. If this variable appears in the current 'Renamer',
-- it is replaced with the corresonding new name. Otherwise, a 'Fresh' variable with a unique ID is
-- generated and added to the 'Renamer'.
renameVar :: (TermEntry a, MonadUnification m) => Var a -> RenamedT m (Var a)
renameVar x = get >>= \m -> case M.lookup x m of
  Just x' -> return x'
  Nothing -> do
    freshX <- lift fresh
    put $ M.insert x freshX m
    return freshX

-- | Rename all of the variables in a term.
renameTerm :: MonadUnification m => Term a -> RenamedT m (Term a)
renameTerm (Variable x) = liftM Variable $ renameVar x
renameTerm (Constant c) = return $ Constant c
renameTerm (Tup tup) = liftM Tup $ renameTuple tup
  where renameTuple :: MonadUnification m => TupleTerm a -> RenamedT m (TupleTerm a)
        renameTuple (Tuple2 t1 t2) = do
          t1' <- renameTerm t1
          t2' <- renameTerm t2
          return $ Tuple2 t1' t2'
        renameTuple (TupleN t ts) = do
          t' <- renameTerm t
          ts' <- renameTuple ts
          return $ TupleN t' ts'
renameTerm (List l) = liftM List $ renameList l
  where renameList :: MonadUnification m => ListTerm a -> RenamedT m (ListTerm a)
        renameList (Cons t ts) = do
          t' <- renameTerm t
          ts' <- renameList ts
          return $ Cons t' ts'
        renameList (VarCons t x) = do
          t' <- renameTerm t
          x' <- renameVar x
          return $ VarCons t' x'
        renameList Nil = return Nil
renameTerm (Constructor c arg) = liftM (Constructor c) $ renameETermList arg
  where renameETermList :: MonadUnification m => [ErasedTerm] -> RenamedT m [ErasedTerm]
        renameETermList [] = return []
        renameETermList (ETerm t : ts) = do
          t' <- renameTerm t
          t'' <- renameETermList ts
          return $ ETerm t' : t''
renameTerm (Sum t1 t2) = renameBinaryTerm Sum t1 t2
renameTerm (Difference t1 t2) = renameBinaryTerm Difference t1 t2
renameTerm (Product t1 t2) = renameBinaryTerm Product t1 t2
renameTerm (Quotient t1 t2) = renameBinaryTerm Quotient t1 t2
renameTerm (IntQuotient t1 t2) = renameBinaryTerm IntQuotient t1 t2
renameTerm (Modulus t1 t2) = renameBinaryTerm Modulus t1 t2

-- | Helper function for renaming variables in a 'Term' with two subterms.
renameBinaryTerm :: MonadUnification m =>
                    (Term a -> Term b -> Term c) -> Term a -> Term b -> RenamedT m (Term c)
renameBinaryTerm constr t1 t2 = do
  rt1 <- renameTerm t1
  rt2 <- renameTerm t2
  return $ constr rt1 rt2

-- | Rename all of the variables in a predicate.
renamePredicate :: MonadUnification m => Predicate -> RenamedT m Predicate
renamePredicate (Predicate name arg) = liftM (Predicate name) $ renameTerm arg

-- | Rename all of the variables in a goal.
renameGoal :: MonadUnification m => Goal -> RenamedT m Goal
renameGoal (PredGoal p cs) = renamePredicate p >>= \p' -> return (PredGoal p' cs)
renameGoal (CanUnify t1 t2) = renameBinaryGoal CanUnify t1 t2
renameGoal (Identical t1 t2) = renameBinaryGoal Identical t1 t2
renameGoal (Equal t1 t2) = renameBinaryGoal Equal t1 t2
renameGoal (LessThan t1 t2) = renameBinaryGoal LessThan t1 t2
renameGoal (Not g) = liftM Not $ renameGoal g
renameGoal (And g1 g2) = do
  g1' <- renameGoal g1
  g2' <- renameGoal g2
  return $ And g1' g2'
renameGoal (Or g1 g2) = do
  g1' <- renameGoal g1
  g2' <- renameGoal g2
  return $ Or g1' g2'
renameGoal Top = return Top
renameGoal Bottom = return Bottom
renameGoal (Alternatives x g xs) = do
  x' <- renameTerm x
  g' <- renameGoal g
  xs' <- renameTerm xs
  return $ Alternatives x' g' xs'
renameGoal (Once g) = liftM Once $ renameGoal g
renameGoal Cut = return Cut

-- | Helper function for renaming variables in a 'Goal' with two 'Term' arguments.
renameBinaryGoal :: MonadUnification m =>
                    (Term a -> Term b -> Goal) -> Term a -> Term b -> RenamedT m Goal
renameBinaryGoal constr t1 t2 = do
  t1' <- renameTerm t1
  t2' <- renameTerm t2
  return $ constr t1' t2'

-- | Rename all of the variables in a clause.
renameClause :: MonadUnification m => HornClause -> m HornClause
renameClause (HornClause p n) = runRenamedT rename
  where rename = do rp <- renamePredicate p
                    rn <- renameGoal n
                    return $ HornClause rp rn
