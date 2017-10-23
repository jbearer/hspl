{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.Solver
Description : The main automated proof engine.
Stability   : Internal

This module defines the resolution proof engine. The engine consists of an algorithm which takes an
HSPL program (a set of clauses) and a goal (a predicate) as input, and outputs a set of proofs of
theorems which all unify with the goal coupled with unifiers accumulated during each proof.

This module also provides various high-level methods for inspecting proof results, depending on the
exact information and level of detail that the client is interested in.
-}
module Control.Hspl.Internal.Solver (
  -- * Proofs
    Theorem
  , ProofResult (..)
  , queryTheorem
  , queryVar
  , getTheorem
  , getAllTheorems
  , runHspl
  , runHsplN
  -- * Solver
  -- ** The Solver monad
  -- *** Class
  , MonadSolver (..)
  , getResult
  -- *** Monad transformer
  , SolverT
  , observeAllSolverT
  , observeManySolverT
  -- *** Monad
  , Solver
  , observeAllSolver
  , observeManySolver
  -- ** The proof-generating algorithm
  , provePredicate
  , proveUnifiable
  , proveIdentical
  , proveEqual
  , proveLessThan
  , proveIsUnified
  , proveIsVariable
  , proveAnd
  , proveOrLeft
  , proveOrRight
  , proveTop
  , proveBottom
  , proveOnce
  , proveIf
  , proveAlternatives
  , proveCut
  , proveCutFrame
  , proveTrack
  , prove
  ) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State
import Data.Data
import Data.Maybe
import Data.Monoid (mempty)

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Logic
import Control.Hspl.Internal.Unification hiding (Unified)

-- | The output of the solver. Contains information about theorems which were proven and variables
-- which were unified during the proof.
data ProofResult = ProofResult { mainTheorem :: Goal
                               , trackedTheorems :: [Goal]
                               , unifiedVars :: Unifier
                               }
  deriving (Show, Eq)

-- | Lookup the status of a variable in a 'ProofResult'.
--
-- Note: querying for variables not present in the initial goal is undefined behavior.
-- TODO: more robust semantics for unknown vars.
queryVar :: TermEntry a => ProofResult -> Var a -> UnificationStatus a
queryVar ProofResult {..} = findVar unifiedVars

-- | Return the list of all tracked theorems proven in the given 'ProofResult' which unify with the
-- given 'Goal'.
queryTheorem :: ProofResult -> Goal -> [Goal]
queryTheorem ProofResult {..} target = do
  g <- trackedTheorems
  let g' = unify unifiedVars g
  let mg = matchGoal g' target
  guard $ isJust mg
  return $ fromJust mg
  where
    -- Unify a goal with the query goal and return the unified goal, or Nothing
    matchGoal (PredGoal prd@(Predicate loc scope name arg) _)
              (PredGoal (Predicate loc' scope' name' arg') _)
      | loc == loc' && scope == scope' && name == name' = case cast arg' >>= mgu arg of
          Just u -> Just $ PredGoal (unify u prd) []
          Nothing -> Nothing
      | otherwise = Nothing
    matchGoal (CanUnify t1 t2) (CanUnify t1' t2') = matchBinary CanUnify (t1, t2) (t1', t2')
    matchGoal (Identical t1 t2) (Identical t1' t2') = matchBinary Identical (t1, t2) (t1', t2')
    matchGoal (Equal t1 t2) (Equal t1' t2') = matchBinary Equal (t1, t2) (t1', t2')
    matchGoal (LessThan t1 t2) (LessThan t1' t2') =
      matchBinary LessThan (toTerm t1, toTerm t2) (toTerm t1', toTerm t2')
    matchGoal g@(IsUnified t) (IsUnified t') = cast t' >>= mgu t >>= \u -> return $ unify u g
    matchGoal g@(IsVariable t) (IsVariable t') = cast t' >>= mgu t >>= \u -> return $ unify u g
    matchGoal (And g1 g2) (And g1' g2') = do g1'' <- matchGoal g1 g1'
                                             g2'' <- matchGoal g2 g2'
                                             return $ And g1'' g2''
    matchGoal (Or g1 g2) (Or g1' g2') = do g1'' <- matchGoal g1 g1'
                                           g2'' <- matchGoal g2 g2'
                                           return $ Or g1'' g2''
    matchGoal Top Top = Just Top
    matchGoal Bottom Bottom = Just Bottom
    matchGoal (Once g) (Once g') = Once `fmap` matchGoal g g'
    matchGoal (If c t f) (If c' t' f') = liftM3 If (matchGoal c c') (matchGoal t t') (matchGoal f f')
    matchGoal (Alternatives n x g xs) (Alternatives n' x' g' xs')
      | n /= n' = Nothing
      | otherwise =
        let t = toTerm (x, xs)
            t' = toTerm (x', xs')
        in case cast t' >>= mgu t of
          Just u -> do
            g'' <- matchGoal g g'
            return $ Alternatives n (unify u x) g'' (unify u xs)
          Nothing -> Nothing

    matchGoal Cut Cut = Just Cut
    matchGoal (CutFrame g) (CutFrame g') = CutFrame `fmap` matchGoal g g'

    matchGoal (Track g) (Track g') = Track `fmap` matchGoal g g'

    matchGoal _ _ = Nothing

    matchBinary :: (TermEntry a, TermEntry b, TermEntry c, TermEntry d) =>
                   (Term a -> Term b -> Goal) -> (Term a, Term b) -> (Term c, Term d) -> Maybe Goal
    matchBinary constr (t1, t2) (t1', t2') =
      let t = toTerm (t1, t2)
          t' = toTerm (t1', t2')
      in case cast t' >>= mgu t of
        Just u -> Just $ unify u $ constr t1 t2
        Nothing -> Nothing

-- | Get the theorem which follows from a 'Proof'; i.e., the root of a proof tree.
getTheorem :: ProofResult -> Goal
getTheorem ProofResult {..} = unify unifiedVars mainTheorem

-- | Get the set of theorems which were proven by each 'Proof' tree in a forest.
getAllTheorems :: [ProofResult] -> [Goal]
getAllTheorems = map getTheorem

-- | Attempt to prove the given 'Goal'. This function returns a forest of 'Proof' trees. If the
-- goal cannot be proven, the result is @[]@. Otherwise, the contents of the resulting list
-- represent various alternative ways of proving the theorem. If there are variables in the goal,
-- they may unify with different values in each alternative proof.
runHspl :: Goal -> [ProofResult]
runHspl g = observeAllSolver (prove g >>= getResult) ()

-- | Extract a 'ProofResult' for a list of proven theorems. The top-level theorem should be at the
-- head of the list.
getResult :: MonadSolver m => Goal -> m ProofResult
getResult thm = do
  u <- getUnifier
  thms <- getRecordedThms
  return ProofResult { mainTheorem = thm
                     , trackedTheorems = thms
                     , unifiedVars = u
                     }

-- | Like 'runHspl', but return at most the given number of proofs.
runHsplN :: Int -> Goal -> [ProofResult]
runHsplN n g = observeManySolver n (prove g >>= getResult) ()

data SolverState s = SolverState { clientState :: s
                                 , freshCount :: Int
                                 , currentUnifier :: Unifier
                                 , provenTheorems :: [Theorem]
                                 }

instance SplittableState s => SplittableState (SolverState s) where
  type GlobalState (SolverState s) = (GlobalState s, Int)
  type BacktrackingState (SolverState s) = (BacktrackingState s, Unifier, [Theorem])
  splitState SolverState {..} =
    let (cBs, cGs) = splitState clientState
    in ((cBs, currentUnifier, provenTheorems), (cGs, freshCount))
  combineState (cBs, u, thms) (cGs, f) = SolverState { clientState = combineState cBs cGs
                                                     , freshCount = f
                                                     , currentUnifier = u
                                                     , provenTheorems = thms
                                                     }

-- | The monad which defines the backtracking control flow of the solver. This type is parameterized
-- by the type of backtracking and global state, implementing the 'MonadLogicState' interface.
newtype SolverT s m a = SolverT { unSolverT :: LogicT (SolverState s) m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadIO, MonadLogic, MonadLogicCut)

instance MonadTrans (SolverT s) where
  lift = SolverT . lift

instance (SplittableState s, Monad m) => MonadVarGenerator (SolverT s m) where
  fresh = do
    f <- SolverT $ gets freshCount
    SolverT $ modify $ \s -> s { freshCount = f + 1 }
    return $ Fresh f

instance (SplittableState s, Monad m) => MonadUnification (SolverT s m) where
  stateUnifier f = do
    u <- SolverT $ gets currentUnifier
    let (r, u') = f u
    SolverT $ modify $ \s -> s { currentUnifier = u' }
    return r

instance (Monad m, SplittableState s) => MonadState s (SolverT s m) where
  get = SolverT $ gets clientState
  put s = SolverT $ modify $ \st -> st { clientState = s }

-- | A non-transformer version of 'SolverT'.
type Solver s = SolverT s Identity

-- | Get all results from a 'Solver' computation.
observeAllSolver :: SplittableState s => Solver s a -> s -> [a]
observeAllSolver m s = runIdentity $ observeAllSolverT m s

-- | Get the specified number of results from a 'Solver' computation.
observeManySolver :: SplittableState s => Int -> Solver s a -> s -> [a]
observeManySolver n m s = runIdentity $ observeManySolverT n m s

-- | Run a 'SolverT' transformed computation, and return a computation in the underlying monad for
-- each solution to the logic computation.
observeAllSolverT :: (Monad m, SplittableState s) => SolverT s m a -> s -> m [a]
observeAllSolverT m s = observeAllLogicT (unSolverT m) SolverState { clientState = s
                                                                   , freshCount = 0
                                                                   , currentUnifier = mempty
                                                                   , provenTheorems = []
                                                                   }

-- | Like 'observeAllSolverT', but limits the number of results returned.
observeManySolverT :: (Monad m, SplittableState s) => Int -> SolverT s m a -> s -> m [a]
observeManySolverT n m s = observeManyLogicT n (unSolverT m) SolverState { clientState = s
                                                                         , freshCount = 0
                                                                         , currentUnifier = mempty
                                                                         , provenTheorems = []
                                                                         }

-- | A proven logical statement. A 'Theorem' is just a 'Goal' that has been proven by the solver.
type Theorem = Goal

-- | This class encapsulates the algorithms required for proving each type of 'Goal'. The proof-
-- generating algorithm defined by 'prove' uses these functions to prove the goal specified by the
-- user and any sub-goal. Each algorithm has an associated "zero-overhead" version -- for example,
-- 'tryPredicate' and 'provePredicateWith'. These represent the minimal work needed to prove a
-- certain type of goal. But monads of this class can define more complex behavior; see the
-- "Control.Hspl.Internal.Debugger" for an example.
class (MonadUnification m, MonadLogicCut m) => MonadSolver m where
  recordThm :: Theorem -> m ()
  getRecordedThms :: m [Theorem]
  -- | Attempt to prove a predicate using the first alternative (the first 'HornClause' with a
  -- matching positive literal). In addition to effects performed in the monad, this computation
  -- should have the following semantics:
  --
  --   1. Attempt to unify the predicate with the positive literal of the clause.
  --   2. Apply the resulting unifier to each negative literal of the clause.
  --   3. Attempt to prove each negative literal, producing a sub-proof for each.
  --   4. Combine the sub-proofs into a 'Resolved' proof.
  --
  -- The zero-overhead version is 'provePredicate'.
  tryPredicate :: Predicate -> HornClause -> m Theorem
  -- | Attempt to prove a predicate using subsequent alternatives. 'retryPredicate' should have the
  -- same semantics as 'tryPredicate', modulo side-effects. The zero-overhead version is
  -- 'provePredicate'.
  retryPredicate :: Predicate -> HornClause -> m Theorem
  -- | Attempt to prove that two terms can be unified. The resulting computation should either fail
  -- with 'mzero' or produce a unifier and a trivial proof of the unified terms. The zero-overhead
  -- version is 'proveUnifiable'.
  tryUnifiable :: TermEntry a => Term a -> Term a -> m Theorem
  -- | Attempt to prove that two terms are identical. No new unifications are created. The resulting
  -- computation should either fail with 'mzero' or produce a trivial proof of the equality of the
  -- terms. The zero-overhead version is 'proveIdentical'.
  tryIdentical :: TermEntry a => Term a -> Term a -> m Theorem
  -- | Attempt to prove equality of terms. The resulting computation should evaluate the right-hand
  -- side and, if successful, attempt to unify the resulting constant with the 'Term' on the left-
  -- hand side. If the right- hand side does not evaluate to a constant (for example, because it
  -- contains one or more free variables) the program should terminate with a runtime error as if by
  -- invoking 'errorUninstantiatedVariables'. The zero-overhead version is 'proveEqual'.
  tryEqual :: TermEntry a => Term a -> Term a -> m Theorem
  -- | Attempt to prove one 'Term' is less than another. No new unifications are created. The
  -- resulting computation should evaluate both terms and, if successful, succeed if the evaluated
  -- left-hand side compares less than the evaluated right-hand side. If /either/ side does not
  -- evaluate to a constant, the program should terminate with a runtime error as if by invoking
  -- 'errorUninstantiatedVariables'. The zero-overhead version is 'proveLessThan'.
  tryLessThan :: (TermEntry a, Ord a) => Term a -> Term a -> m Theorem
  -- | Attempt to prove that a 'Term' is fully unified (i.e. it recursively contains no variables).
  -- No new unifications are created. The zero-overhead version is 'proveIsUnified'.
  tryIsUnified :: TermEntry a => Term a -> m Theorem
  -- | Attempt to prove that a 'Term' is an uninstantiated variable. No new unfications are created.
  -- The zero-overhead version is 'proveIsVariable'.
  tryIsVariable :: TermEntry a => Term a -> m Theorem
  -- | Attempt to prove the conjunction of two goals. The resulting computation should succeed,
  -- emitting a 'ProvedAnd' result with subproofs for each subgoal, if and only if both subgoals
  -- succeed. Further, it is important that unifications made while proving the left-hand side are
  -- applied to the right-hand side before proving it. The zero-overhead version is 'proveAnd'.
  tryAnd :: Goal -> Goal -> m Theorem
  -- | Attempt to prove the first subgoal in a disjunction. The resulting computation should either
  -- fail with 'mzero', or emit a 'ProvedLeft' proof for each time the left subgoal succeeds. The
  -- zero-overhead version is 'proveOrLeft'.
  tryOrLeft :: Goal -> Goal -> m Theorem
  -- | Attempt to prove the second subgoal in a disjunction. The resulting computation should have
  -- the same semantics as 'tryOr', modulo effects in the underlying monad and the fact that it
  -- emits 'provedRight' proofs rather than 'provedLeft' proofs. The zero-overhead version is
  -- 'proveOrRight'.
  tryOrRight :: Goal -> Goal -> m Theorem
  -- | Emit a proof of 'Top'. This computation should always succeed with 'ProvedTop', perhaps after
  -- performing side-effects in the monad. The zero- overhead version is 'proveTop'.
  tryTop :: m Theorem
  -- | Attempt to prove 'Bottom'. This computation should always fail with 'mzero', perhaps after
  -- performing effects in the monad. The zero-overhead version is 'proveBottom'.
  tryBottom :: m Theorem
  -- | Attempt to prove a 'Once' goal.The resulting computation should succeed exactly once if the
  -- argument succeeds at all, and should have the same semantics as proving the first result of the
  -- argument would have. If the argument fails, the 'Once' goal should also fail. The zero-overhead
  -- version is 'proveOnce'.
  tryOnce :: Goal -> m Theorem
  -- | Attempt to prove an 'If' goal. The semantics of @If c t f@ should satisfy the following
  -- properties:
  --
  -- If @c@ succeeds at all, the computation should satisfy
  --
  -- prop> tryIf c t f = tryAnd c t
  --
  -- If @c@ fails, the computation should satisfy
  --
  -- prop> tryIf c t f = tryOr c f
  --
  -- The zero-overhead version is 'proveIf'.
  tryIf :: Goal -> Goal -> Goal -> m Theorem
  -- | Attempt to prove an 'Alternatives' goal. In addition to any effects performed in the monad,
  -- this computation should have the following semantics:
  --
  --   1. If the first parameter is 'Nothing', obtain all solutions of the inner goal, as if through
  --   'runHspl'. Otherwise, obtain at most the indicated number of solutions, as if through
  --   'runHsplN'.
  --   2. For each solution, apply the unifier to the template 'Term' (first argument).
  --   3. Attempt to unify the resulting list with the output 'Term' (third argument).
  --
  -- The proof should succeed if and only if step 3 succeeds. In particular, note that the failure
  -- of the inner goal does not imply the failure of the proof. It should simply try to unify an
  -- empty list with the output term.
  --
  -- The zero-overhead version is 'proveAlternatives'.
  tryAlternatives :: TermEntry a => Maybe Int -> Term a -> Goal -> Term [a] -> m Theorem
  -- | Emit a proof of 'Cut'. This computation always succeeds, and the proof is always trivial.
  -- However, it should perform the side-effect of discarding all unexplored choicepoints created
  -- since entering the last 'CutFrame'. The zero-overhead version is 'proveCut'.
  tryCut :: m Theorem
  -- | Attempt to prove the given goal in a new cut frame. The proof proceeds as norm, except that
  -- if 'Cut' is encountered during the proof, it does not affect choice points created since
  -- entering the 'CutFrame' goal. The zero-overhead version is 'proveCutFrame'.
  tryCutFrame :: Goal -> m Theorem
  -- | Attempt to prove a 'Track' goal. This computation should succeed whenever the inner goal
  -- does. It should then return a list consisting of any theorems proven in the inner goal, as well
  -- as the inner goal itself. The inner goal should be at the head of the list. The zero-overhead
  -- version is 'proveTrack'.
  tryTrack :: Goal -> m Theorem
  -- | Computation to be invoked when a goal fails because there are no matching clauses. This
  -- computation should result in 'mzero', but may perform effects in the underlying monad first.
  failUnknownPred :: Predicate -> m Theorem
  -- | Computation to be invoked when attempting to evaluate a 'Term' which contains ununified
  -- variables. As the type suggests, this should result in a call to 'error'.
  errorUninstantiatedVariables :: m a

instance (SplittableState s, Monad m) => MonadSolver (SolverT s m) where
  recordThm thm = SolverT $ modify $ \st -> st { provenTheorems = thm : provenTheorems st }
  getRecordedThms = SolverT $ gets provenTheorems
  tryPredicate = provePredicate
  retryPredicate = provePredicate
  tryUnifiable = proveUnifiable
  tryIdentical = proveIdentical
  tryEqual = proveEqual
  tryLessThan = proveLessThan
  tryIsUnified = proveIsUnified
  tryIsVariable = proveIsVariable
  tryAnd = proveAnd
  tryOrLeft = proveOrLeft
  tryOrRight = proveOrRight
  tryTop = proveTop
  tryBottom = proveBottom
  tryOnce = proveOnce
  tryIf = proveIf
  tryAlternatives = proveAlternatives
  tryCut = proveCut
  tryCutFrame = proveCutFrame
  tryTrack = proveTrack
  failUnknownPred = const mzero
  errorUninstantiatedVariables = error "Variables are not sufficiently instantiated."

-- | Zero-overhead version of 'tryPredicate' and 'retryPredicate'.
provePredicate :: MonadSolver m => Predicate -> HornClause -> m Theorem
provePredicate p c = do
  let predGoal = PredGoal p [c]
  g <- resolve p c
  case g of
    -- Exit early (without invoking any continuations) if the subgoal is Top. This isn't strictly
    -- necessary; if we were to invoke the continuation on Top it would just succeed immediately.
    -- But we want to give any observers the appearance of this goal succeeding immediately, with no
    -- further calls. It just makes the control flow a bit more intuitive (i.e. more similar to
    -- Prolog's)
    Top -> return predGoal
    _ -> prove g >> return predGoal

-- | Zero-overhead version of 'tryUnifiable'.
proveUnifiable :: (TermEntry a, MonadSolver m) => Term a -> Term a -> m Theorem
proveUnifiable t1 t2 = case mgu t1 t2 of
  Just u -> addUnifier u >> return (CanUnify t1 t2)
  Nothing -> mzero

-- | Zero-overhead version of 'tryIdentical'.
proveIdentical :: (TermEntry a, MonadSolver m) => Term a -> Term a -> m Theorem
proveIdentical t1 t2
  | t1 == t2 = return $ Identical t1 t2
  | otherwise = mzero

-- | Zero-overhead version of 'tryEqual'.
proveEqual :: (TermEntry a, MonadSolver m) => Term a -> Term a -> m Theorem
proveEqual lhs rhs = do
  rhs' <- eval rhs
  case mgu lhs rhs' of
    Just u -> addUnifier u >> return (Equal lhs rhs')
    Nothing -> mzero
  where eval t = case fromTerm t of
          Just t' -> return $ toTerm t'
          Nothing -> errorUninstantiatedVariables

-- | Zero-overhead version of 'tryLessThan'.
proveLessThan :: (TermEntry a, Ord a, MonadSolver m) => Term a -> Term a -> m Theorem
proveLessThan lhs rhs = case (fromTerm lhs, fromTerm rhs) of
  (Just l, Just r) | l < r -> return $ LessThan (toTerm l) (toTerm r)
  (Just _, Just _) -> mzero
  _ -> errorUninstantiatedVariables

-- | Zero-overhead version of 'tryIsUnified'.
proveIsUnified :: (TermEntry a, MonadSolver m) => Term a -> m Theorem
proveIsUnified t = if isJust (fromTerm t) then return (IsUnified t) else mzero

-- | Zero-overhead version of 'tryIsVariable'.
proveIsVariable :: (TermEntry a, MonadSolver m) => Term a -> m Theorem
proveIsVariable t@(Variable _) = return $ IsVariable t
proveIsVariable _ = mzero

-- | Zero-overhead version of 'tryAnd'.
proveAnd :: MonadSolver m => Goal -> Goal -> m Theorem
proveAnd g1 g2 = liftM2 And (prove g1) (prove =<< munify g2)

-- | Zero-overhead version of 'tryOrLeft'.
proveOrLeft :: MonadSolver m => Goal -> Goal -> m Theorem
proveOrLeft g1 g2 = prove g1 >>= \thm -> return $ Or thm g2

-- | Zero-overhead version of 'tryOrRight'.
proveOrRight :: MonadSolver m => Goal -> Goal -> m Theorem
proveOrRight g1 g2 = prove g2 >>= \thm -> return $ Or g1 thm

-- | Zero-overhead version of 'tryTop'.
proveTop :: Monad m => m Theorem
proveTop = return Top

-- | Zero-overhead version of 'tryBottom'.
proveBottom :: MonadSolver m => m Theorem
proveBottom = mzero

-- | Zero-overhead version of 'tryOnce'.
proveOnce :: MonadSolver m => Goal -> m Theorem
proveOnce = liftM Once . once . prove

-- | Zero-overhead version of 'tryIf'.
proveIf :: MonadSolver m => Goal -> Goal -> Goal -> m Theorem
proveIf c t f = ifte (prove c) (\cthm -> prove t >>= \tthm -> return $ If cthm tthm f)
                               (prove f >>= \fthm -> return $ If c t fthm)

-- | Zero-overhead version of 'tryAlternatives'.
proveAlternatives :: (MonadSolver m, TermEntry a) =>
                     Maybe Int -> Term a -> Goal -> Term [a] -> m Theorem
proveAlternatives maybeN x g xs = do
  results <- getAlternatives maybeN $ prove g
  -- Since we threw out local unifications, we must unify the local theorems now
  let (thms, us) = unzip [(map (unify localU) ts, localU) | (ts, localU) <- results]
  forM_ (concat thms) recordThm
  let alternatives = toTerm $ map (`unify` x) us
  let mu = mgu xs alternatives
  guard $ isJust mu
  addUnifier $ fromJust mu
  return $ Alternatives maybeN x g xs
  where getAlternatives mn m =
          let m' = m >> liftM2 (,) getRecordedThms getUnifier
          in case mn of
            Just n -> extractN n m'
            Nothing -> extractAll m'
        extractN n m
          | n <= 0 = return []
          | otherwise = extract (extractN $ n-1) m
        extractAll = extract extractAll
        extract next m = do split <- msplit m
                            case split of
                              Just (a, fk) -> (a:) `liftM` next fk
                              Nothing -> return []

-- | Zero-overhead version of 'tryCut'.
proveCut :: MonadSolver m => m Theorem
proveCut = commit Cut

-- | Zero-overhead version of 'tryCutFrame'.
proveCutFrame :: MonadSolver m => Goal -> m Theorem
proveCutFrame g = CutFrame `liftM` cutFrame (prove g)

-- | Zero-overhead version of 'tryTrack'.
proveTrack :: MonadSolver m => Goal -> m Theorem
proveTrack g = do
  thm <- prove g
  recordThm thm
  return $ Track thm

-- | Produce a proof of the goal. This function will either fail, or backtrack over all possible
-- proofs. It will invoke the appropriate continuations in the given 'SolverCont' whenever a
-- relevant event occurs during the course of the proof.
prove :: MonadSolver m => Goal -> m Theorem
prove g = case g of
  PredGoal p [] -> failUnknownPred p
  PredGoal p (c:cs) -> cutFrame $ tryPredicate p c `mplus` msum (map (retryPredicate p) cs)
  CanUnify t1 t2 -> tryUnifiable t1 t2
  Identical t1 t2 -> tryIdentical t1 t2
  Equal t1 t2 -> tryEqual t1 t2
  LessThan t1 t2 -> tryLessThan t1 t2
  IsUnified t -> tryIsUnified t
  IsVariable t -> tryIsVariable t
  And g1 g2 -> tryAnd g1 g2
  Or g1 g2 -> tryOrLeft g1 g2 `mplus` tryOrRight g1 g2
  Top -> tryTop
  Bottom -> tryBottom
  Once g' -> tryOnce g'
  If c t f -> tryIf c t f
  Alternatives n x g' xs -> tryAlternatives n x g' xs
  Cut -> tryCut
  CutFrame g' -> tryCutFrame g'
  Track g' -> tryTrack g'
