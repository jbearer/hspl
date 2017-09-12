{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
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
  , findVar
  , isSubunifierOf
  -- * Unification
  -- ** The unification monad
  , MonadVarGenerator (..)
  , VarGeneratorT
  , runVarGeneratorT
  , VarGenerator
  , runVarGenerator
  , MonadUnification (..)
  , modifyUnifier
  , addUnifier
  , munify
  -- ** Unification algorithm
  , Unifiable (..)
  , freeIn
  , mgu
  , resolve
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

import Control.Exception
import Control.Monad.Identity
import Control.Monad.State
import Data.Typeable

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.VarMap (VarMap)
import qualified Control.Hspl.Internal.VarMap as M

-- | Class of monads capable of generating global unique variables.
class Monad m => MonadVarGenerator m where
  -- | Get a 'Fresh' variable.
  fresh :: TermEntry a => m (Var a)

-- | Monad transformer for generating unique variables.
type VarGeneratorT = StateT Int

instance Monad m => MonadVarGenerator (VarGeneratorT m) where
  fresh = do
    f <- get
    put $ f + 1
    return $ Fresh f

-- | Run a 'VarGeneratorT' computation.
runVarGeneratorT :: Monad m => VarGeneratorT m a -> m a
runVarGeneratorT m = evalStateT m 0

-- | Non-transformer version of 'VarGeneratorT'.
type VarGenerator = VarGeneratorT Identity

-- | Run a 'VarGenerator' computation.
runVarGenerator :: VarGenerator a -> a
runVarGenerator = runIdentity . runVarGeneratorT

-- | Monad in which all unification operations take place. All unifications in a single run of an
-- HSPL program should take place in the same 'MonadUnification' computation.
class (MonadVarGenerator m, MonadPlus m) => MonadUnification m where
  -- | Embed a computation which is stateful in the current 'Unifier' into the monad.
  stateUnifier :: (Unifier -> (a, Unifier)) -> m a
  stateUnifier f = do
    u <- getUnifier
    let (r, u') = f u
    putUnifier u'
    return r

  -- | Retrieve the current 'Unifier'.
  getUnifier :: m Unifier
  getUnifier = stateUnifier (\u -> (u, u))

  -- | Set the current 'Unifier'.
  putUnifier :: Unifier -> m ()
  putUnifier u = stateUnifier $ const ((), u)

  {-# MINIMAL (stateUnifier | getUnifier, putUnifier) #-}

-- | Update the current 'Unifier' based on a supplied transformation function.
modifyUnifier :: MonadUnification m => (Unifier -> Unifier) -> m ()
modifyUnifier f = (f `liftM` getUnifier) >>= putUnifier

-- | Add the unifications contained in the given 'Unifier' to the current 'Unifier'. This function
-- will update existing unifications if the substituting term contains a variable which is
-- substitued for in the new 'Unifier'. (See 'compose' for details on the semantics of udpating
-- 'Unifier's.)
addUnifier :: MonadUnification m => Unifier -> m ()
addUnifier u = modifyUnifier (`compose` u)

-- | Types to which a 'Unifier' can be applied.
class Unifiable a where
  -- | Apply the given 'Unifier', replacing all free variables with the value associated with that
  -- variable in the 'Unifier'.
  unify :: Unifier -> a -> a

-- | Unify a given 'Unifiable' using the current value of the 'Unifier' from the 'MonadUnification'
-- computation.
munify :: (MonadUnification m, Unifiable a) => a -> m a
munify a = (`unify` a) `liftM` getUnifier

-- | A unifier maps variables to terms which are to replace those variables.
type Unifier = VarMap Term

-- | Compute the composition of two 'Unifier's. This is the net unification that results from
-- applying the first unifier and then the second in sequence.
infixr 6 `compose` -- Same as <> for Monoid
compose :: Unifier -> Unifier -> Unifier
compose u1 u2 = M.map (unify u2) u1 `M.union` u2

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
mgu (Variable Anon) _ = Just M.empty
mgu _ (Variable Anon) = Just M.empty
mgu (Variable x) (Variable y)
  | x == y = Just M.empty -- no occurs check if we're unifying two variables
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
                                                          let uts = map (termMap $ ETerm . unify u) ts
                                                          let uts' = map (termMap $ ETerm . unify u) ts'
                                                          u' <- mguETermList uts uts'
                                                          return $ u `compose` u'

mgu (Tup tup) (Tup tup') = mguTup tup tup'
  where mguTup :: TermEntry a => TupleTerm a -> TupleTerm a -> Maybe Unifier
        mguTup (Tuple2 t1 t2) (Tuple2 t1' t2') = mguBinaryTerm (t1, t2) (t1', t2')
        mguTup (TupleN t ts) (TupleN t' ts') = do u <- mgu t t'
                                                  let uts = unify u ts
                                                  let uts' = unify u ts'
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
mguBinaryTerm :: (TermEntry a, TermEntry b) => (Term a, Term b) -> (Term a, Term b) -> Maybe Unifier
mguBinaryTerm (t1, t2) (t1', t2') = do
  -- Unify the subterms in sequence, applying each intermediate unifier to the remaining terms
  mgu1 <- mgu t1 t1'
  let ut2 = unify mgu1 t2
  let ut2' = unify mgu1 t2'
  mgu2 <- mgu ut2 ut2'
  return $ mgu1 `compose` mgu2

instance TermEntry a => Unifiable (TupleTerm a) where
  unify u (Tuple2 t1 t2) = Tuple2 (unify u t1) (unify u t2)
  unify u (TupleN t ts) = TupleN (unify u t) (unify u ts)

instance TermEntry a => Unifiable (Term a) where
  unify u v@(Variable x) = M.findWithDefault v x u
  unify _ c@(Constant _) = c
  unify u (Constructor c ts) = Constructor c $ map (termMap $ ETerm . unify u) ts
  unify u (Tup t) = Tup $ unify u t
  unify unifier (List l) = List $ unifyList unifier l
    where unifyList :: Unifier -> ListTerm a -> ListTerm a
          unifyList u (Cons t ts) = Cons (unify u t) (unifyList u ts)
          unifyList u (VarCons t x) =
            case getListTerm $ unify u $ Variable x of
              Left ux -> VarCons (unify u t) ux
              Right xs -> Cons (unify u t) xs
          unifyList _ Nil = Nil
  unify u (Sum t1 t2) = Sum (unify u t1) (unify u t2)
  unify u (Difference t1 t2) = Difference (unify u t1) (unify u t2)
  unify u (Product t1 t2) = Product (unify u t1) (unify u t2)
  unify u (Quotient t1 t2) = Quotient (unify u t1) (unify u t2)
  unify u (IntQuotient t1 t2) = IntQuotient (unify u t1) (unify u t2)
  unify u (Modulus t1 t2) = Modulus (unify u t1) (unify u t2)

instance Unifiable Predicate where
  unify u (Predicate name term) = Predicate name (unify u term)

instance Unifiable Goal where
  unify u (PredGoal p cs) = PredGoal (unify u p) cs
  unify u (CanUnify t1 t2) = CanUnify (unify u t1) (unify u t2)
  unify u (Identical t1 t2) = Identical (unify u t1) (unify u t2)
  unify u (Equal t1 t2) = Equal (unify u t1) (unify u t2)
  unify u (LessThan t1 t2) = LessThan (unify u t1) (unify u t2)
  unify u (IsUnified t) = IsUnified $ unify u t
  unify u (IsVariable t) = IsVariable $ unify u t
  unify u (Not g) = Not $ unify u g
  unify u (And g1 g2) = And (unify u g1) (unify u g2)
  unify u (Or g1 g2) = Or (unify u g1) (unify u g2)
  unify _ Top = Top
  unify _ Bottom = Bottom
  unify u (Alternatives x g xs) = Alternatives (unify u x) (unify u g) (unify u xs)
  unify u (Once g) = Once $ unify u g
  unify _ Cut = Cut

instance Unifiable HornClause where
  unify u (HornClause p n) = HornClause (unify u p) (unify u n)

-- | Unify a 'Predicate' with a 'HornClause' with a matching positive literal. Assuming the
-- predicate unifies with the positive literal of the clause, the 'mgu' is applied to the negative
-- literal and the resulting goal is returned. Before unification, the 'HornClause' is renamed apart
-- so that it does not share any free variables with the goal.
resolve :: MonadUnification m => Predicate -> HornClause -> m Goal
resolve (Predicate name arg) c@(HornClause (Predicate name' _) _) =
  assert (name == name') $ do
    HornClause (Predicate _ arg') neg <- renameClause c
    case cast arg' >>= mgu arg of
      Nothing -> mzero
      Just u -> addUnifier u >> munify neg

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
findVar :: TermEntry a => Unifier -> Var a -> UnificationStatus a
findVar u x = case M.lookup x u of
  Nothing -> Ununified
  Just t -> case fromTerm t of
    Nothing -> Partial t
    Just c -> Unified c

-- | A renamer maps variables to 'Fresh' variables with which the former should be renamed.
type Renamer = VarMap Var

-- | Monad encapsulating the state of a renaming operation.
type RenamedT m = StateT Renamer m

-- | Evaluate a computation in a 'RenamedT' monad.
runRenamedT :: MonadVarGenerator m => RenamedT m a -> m a
runRenamedT m = evalStateT m M.empty

-- | Non-transformed version of the 'RenamedT' monad.
type Renamed = RenamedT VarGenerator

-- | Special case of 'runRenamedT' for the plain 'Renamed' monad.
runRenamed :: Renamed a -> a
runRenamed = runVarGenerator . runRenamedT

-- | Replace a variable with a new, unique name. If this variable appears in the current 'Renamer',
-- it is replaced with the corresonding new name. Otherwise, a 'Fresh' variable with a unique ID is
-- generated and added to the 'Renamer'.
renameVar :: (TermEntry a, MonadVarGenerator m) => Var a -> RenamedT m (Var a)
renameVar Anon = return Anon
renameVar x = get >>= \m -> case M.lookup x m of
  Just x' -> return x'
  Nothing -> do
    freshX <- lift fresh
    put $ M.insert x freshX m
    return freshX

-- | Rename all of the variables in a term.
renameTerm :: MonadVarGenerator m => Term a -> RenamedT m (Term a)
renameTerm (Variable x) = liftM Variable $ renameVar x
renameTerm (Constant c) = return $ Constant c
renameTerm (Tup tup) = liftM Tup $ renameTuple tup
  where renameTuple :: MonadVarGenerator m => TupleTerm a -> RenamedT m (TupleTerm a)
        renameTuple (Tuple2 t1 t2) = do
          t1' <- renameTerm t1
          t2' <- renameTerm t2
          return $ Tuple2 t1' t2'
        renameTuple (TupleN t ts) = do
          t' <- renameTerm t
          ts' <- renameTuple ts
          return $ TupleN t' ts'
renameTerm (List l) = liftM List $ renameList l
  where renameList :: MonadVarGenerator m => ListTerm a -> RenamedT m (ListTerm a)
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
  where renameETermList :: MonadVarGenerator m => [ErasedTerm] -> RenamedT m [ErasedTerm]
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
renameBinaryTerm :: MonadVarGenerator m =>
                    (Term a -> Term b -> Term c) -> Term a -> Term b -> RenamedT m (Term c)
renameBinaryTerm constr t1 t2 = do
  rt1 <- renameTerm t1
  rt2 <- renameTerm t2
  return $ constr rt1 rt2

-- | Rename all of the variables in a predicate.
renamePredicate :: MonadVarGenerator m => Predicate -> RenamedT m Predicate
renamePredicate (Predicate name arg) = liftM (Predicate name) $ renameTerm arg

-- | Rename all of the variables in a goal.
renameGoal :: MonadVarGenerator m => Goal -> RenamedT m Goal
renameGoal (PredGoal p cs) = renamePredicate p >>= \p' -> return (PredGoal p' cs)
renameGoal (CanUnify t1 t2) = liftM2 CanUnify (renameTerm t1) (renameTerm t2)
renameGoal (Identical t1 t2) = liftM2 Identical (renameTerm t1) (renameTerm t2)
renameGoal (Equal t1 t2) = liftM2 Equal (renameTerm t1) (renameTerm t2)
renameGoal (LessThan t1 t2) = liftM2 LessThan (renameTerm t1) (renameTerm t2)
renameGoal (IsUnified t) = IsUnified `liftM` renameTerm t
renameGoal (IsVariable t) = IsVariable `liftM` renameTerm t
renameGoal (Not g) = liftM Not $ renameGoal g
renameGoal (And g1 g2) = liftM2 And (renameGoal g1) (renameGoal g2)
renameGoal (Or g1 g2) = liftM2 Or (renameGoal g1) (renameGoal g2)
renameGoal Top = return Top
renameGoal Bottom = return Bottom
renameGoal (Alternatives x g xs) = liftM3 Alternatives (renameTerm x) (renameGoal g) (renameTerm xs)
renameGoal (Once g) = liftM Once $ renameGoal g
renameGoal Cut = return Cut

-- | Rename all of the variables in a clause.
renameClause :: MonadVarGenerator m => HornClause -> m HornClause
renameClause (HornClause p n) = runRenamedT rename
  where rename = do rp <- renamePredicate p
                    rn <- renameGoal n
                    return $ HornClause rp rn
