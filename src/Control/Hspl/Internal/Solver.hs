{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
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
    Proof (..)
  , ProofResult
  , searchProof
  , getUnifier
  , getAllUnifiers
  , getSolution
  , getAllSolutions
  , runHspl
  , runHsplN
  -- * Solver
  -- ** The Solver monad
  -- *** Class
  , MonadSolver (..)
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
  , proveNot
  , proveAnd
  , proveOrLeft
  , proveOrRight
  , proveTop
  , proveBottom
  , proveAlternatives
  , proveOnce
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

-- | Abstract representation of a proof. A proof can be thought of as a tree, where each node is a
-- goal or subgoal which was proven, and the children of that node, if any, are subgoals which
-- together imply the truth of the node. There are various types of nodes (represented by the
-- different 'Proof' constructors) corresponding to the various types of 'Goal's.
data Proof =
             -- | A proof of a 'PredGoal' by the resolution inference rule. The 'Predicate' is the
             -- statement proven, while the 'Proof' is a proof of the predicate's negative literal.
             Resolved Predicate Proof
             -- | A proof of a 'CanUnify' goal.
           | forall a. TermEntry a => Unified (Term a) (Term a)
             -- | A proof of an 'Identical' goal.
           | forall a. TermEntry a => Identified (Term a) (Term a)
             -- | A proof of an 'Equal' goal.
           | forall a. TermEntry a => Equated (Term a) (Term a)
             -- | A proof of a 'LessThan' goal.
           | forall a. (TermEntry a, Ord a) => ProvedLessThan a a
             -- | A proof of a 'Not' goal.
           | Negated Goal
             -- | A proof of an 'And' goal. Contains a proof of each subgoal in the conjunction.
           | ProvedAnd Proof Proof
             -- | A proof of an 'Or' goal. The 'Proof' is a proof of the left subgoal, and the
             -- 'Goal' is the unproven right subgoal.
           | ProvedLeft Proof Goal
             -- | A proof of an 'Or' goal. The 'Proof' is a proof of the right subgoal, and the
             -- 'Goal' is the unproven left subgoal.
           | ProvedRight Goal Proof
             -- | A (trivial) proof of 'Top'.
           | ProvedTop
             -- | A proof of an 'Alternatives' goal. The first argument is the template term, the
             -- second is the subgoal, and the third is the "bag" of alternatives. The final
             -- argument is the list of proofs of the subgoal.
           | forall a. TermEntry a => FoundAlternatives (Term a) Goal (Term [a]) [Proof]
             -- | A proof of a 'Once' goal.
           | ProvedOnce Proof

instance Eq Proof where
  (==) proof1 proof2 = case (proof1, proof2) of
    (Resolved p proof, Resolved p' proof') -> p == p' && proof == proof'
    (Unified t1 t2, Unified t1' t2') -> compareBinaryProof (t1, t2) (t1', t2')
    (Identified t1 t2, Identified t1' t2') -> compareBinaryProof (t1, t2) (t1', t2')
    (Equated t1 t2, Equated t1' t2') -> compareBinaryProof (t1, t2) (t1', t2')
    (ProvedLessThan t1 t2, ProvedLessThan t1' t2') -> compareBinaryProof (t1, t2) (t1', t2')
    (Negated g, Negated g') -> g == g'
    (ProvedAnd p1 p2, ProvedAnd p1' p2') -> p1 == p1' && p2 == p2'
    (ProvedLeft p g, ProvedLeft p' g') -> p == p' && g == g'
    (ProvedRight g p, ProvedRight g' p') -> g == g' && p == p'
    (ProvedTop, ProvedTop) -> True
    (FoundAlternatives x g xs ps, FoundAlternatives x' g' xs' ps') -> fromMaybe False $
      do x'' <- cast x'
         xs'' <- cast xs'
         return $ x == x'' && g == g' && xs == xs'' && ps == ps'
    (ProvedOnce p, ProvedOnce p') -> p == p'
    _ -> False
    where compareBinaryProof t t' = maybe False (t==) $ cast t'

instance Show Proof where
  show (Resolved p proof) = "Resolved (" ++ show p ++ ") (" ++ show proof ++ ")"
  show (Unified t1 t2) = "Unified (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Identified t1 t2) = "Identified (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Equated t1 t2) = "Equated (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
#ifdef SHOW_TERMS
  show (ProvedLessThan t1 t2) = "ProvedLessThan (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
#else
  show (ProvedLessThan t1 t2) =
    "ProvedLessThan (" ++ show (toTerm t1) ++ ") (" ++ show (toTerm t2) ++ ")"
#endif
  show (Negated g) = "Negated (" ++ show g ++ ")"
  show (ProvedAnd p1 p2) = "ProvedAnd (" ++ show p1 ++ ") (" ++ show p2
  show (ProvedLeft p g) = "ProvedLeft (" ++ show p ++ ") (" ++ show g ++ ")"
  show (ProvedRight g p) = "ProvedRight (" ++ show g ++ ") (" ++ show p ++ ")"
  show (FoundAlternatives x g xs ps) =
    "FoundAlternatives (" ++ show x ++ ") (" ++ show g ++ ") (" ++ show xs ++ ") (" ++ show ps ++ ")"
  show ProvedTop = "ProvedTop"
  show (ProvedOnce p) = "ProvedOnce (" ++ show p ++ ")"

-- | The output of the solver. This is meant to be treated as an opaque data type which can be
-- inspected via the functions defined in this module.
type ProofResult = (Proof, Unifier)

-- | Return the list of all goals or subgoals in the given result which unify with a particular goal.
searchProof :: ProofResult -> Goal -> [Goal]
searchProof (proof, unifier) goal = searchProof' proof (runRenamed $ renameGoal goal)
  where searchProof' p g =
          maybeToList (matchGoal (getSolution (p, unifier)) g) ++
          concatMap (`searchProof'` g) (subProofs p)

        subProofs (Resolved _ p) = [p]
        subProofs (ProvedAnd p1 p2) = [p1, p2]
        subProofs (ProvedLeft p _) = [p]
        subProofs (ProvedRight _ p) = [p]
        subProofs (FoundAlternatives _ _ _ ps) = ps
        subProofs (ProvedOnce p) = [p]
        subProofs _ = []

        -- Unify a goal with the query goal and return the unified goal, or Nothing
        matchGoal (PredGoal prd@(Predicate name arg) _) (PredGoal (Predicate name' arg') _)
          | name == name' = case cast arg' >>= mgu arg of
              Just u -> Just $ PredGoal (unifyPredicate u prd) []
              Nothing -> Nothing
          | otherwise = Nothing
        matchGoal (CanUnify t1 t2) (CanUnify t1' t2') = matchBinary CanUnify (t1, t2) (t1', t2')
        matchGoal (Identical t1 t2) (Identical t1' t2') = matchBinary Identical (t1, t2) (t1', t2')
        matchGoal (Equal t1 t2) (Equal t1' t2') = matchBinary Equal (t1, t2) (t1', t2')
        matchGoal (LessThan t1 t2) (LessThan t1' t2') =
          matchBinary LessThan (toTerm t1, toTerm t2) (toTerm t1', toTerm t2')
        matchGoal (Not g) (Not g') = fmap Not $ matchGoal g g'
        matchGoal (And g1 g2) (And g1' g2') = do g1'' <- matchGoal g1 g1'
                                                 g2'' <- matchGoal g2 g2'
                                                 return $ And g1'' g2''
        matchGoal (Or g1 g2) (Or g1' g2') = do g1'' <- matchGoal g1 g1'
                                               g2'' <- matchGoal g2 g2'
                                               return $ Or g1'' g2''
        matchGoal Top Top = Just Top
        matchGoal Bottom Bottom = Just Bottom
        matchGoal (Alternatives x g xs) (Alternatives x' g' xs') =
          let t = toTerm (x, xs)
              t' = toTerm (x', xs')
          in case cast t' >>= mgu t of
            Just u -> do
              g'' <- matchGoal g g'
              return $ Alternatives (unifyTerm u x) g'' (unifyTerm u xs)
            Nothing -> Nothing

        matchGoal (Once g) (Once g') = fmap Once $ matchGoal g g'

        matchGoal _ _ = Nothing

        matchBinary :: (TermEntry a, TermEntry b, TermEntry c, TermEntry d) =>
                       (Term a -> Term b -> Goal) -> (Term a, Term b) -> (Term c, Term d) -> Maybe Goal
        matchBinary constr (t1, t2) (t1', t2') =
          let t = toTerm (t1, t2)
              t' = toTerm (t1', t2')
          in case cast t' >>= mgu t of
            Just u -> Just $ unifyGoal u $ constr t1 t2
            Nothing -> Nothing

-- | Get the 'Unifier' which maps variables in the goal to their final values (the values for which
-- they were substituted in the proven theorem). This unifier can then be queried with 'queryVar' to
-- get the 'UnificationStatus' of each variable.
--
-- Note: querying the unifier for variables not present in the initial goal is undefined behavior.
-- TODO: more robust semantics for unknown vars.
getUnifier :: ProofResult -> Unifier
getUnifier (_, u) = u

-- | Get the 'Unifier' for each 'Proof' of the goal.
getAllUnifiers :: [ProofResult] -> [Unifier]
getAllUnifiers = map getUnifier

-- | Get the theorem which follows from a 'Proof'; i.e., the root of a proof tree.
getSolution :: ProofResult -> Goal
getSolution (proof, _) = case proof of
  Resolved p _ -> PredGoal p []
  Unified t1 t2 -> CanUnify t1 t2
  Identified t1 t2 -> Identical t1 t2
  Equated t1 t2 -> Equal t1 t2
  ProvedLessThan t1 t2 -> LessThan (toTerm t1) (toTerm t2)
  Negated g -> Not g
  ProvedAnd p1 p2 -> And (getSolution (p1, mempty)) (getSolution (p2, mempty))
  ProvedLeft p g -> Or (getSolution (p, mempty)) g
  ProvedRight g p -> Or g (getSolution (p, mempty))
  ProvedTop -> Top
  FoundAlternatives x g xs _ -> Alternatives x g xs
  ProvedOnce p -> Once $ getSolution (p, mempty)

-- | Get the set of theorems which were proven by each 'Proof' tree in a forest.
getAllSolutions :: [ProofResult] -> [Goal]
getAllSolutions = map getSolution

-- | Attempt to prove the given 'Goal'. This function returns a forest of 'Proof' trees. If the
-- goal cannot be proven, the result is @[]@. Otherwise, the contents of the resulting list
-- represent various alternative ways of proving the theorem. If there are variables in the goal,
-- they may unify with different values in each alternative proof.
runHspl :: Goal -> [ProofResult]
runHspl g = observeAllSolver (prove g) ()

-- | Like 'runHspl', but return at most the given number of proofs.
runHsplN :: Int -> Goal -> [ProofResult]
runHsplN n g = observeManySolver n (prove g) ()

-- | The monad which defines the backtracking control flow of the solver. This type is parameterized
-- by the type of backtracking and global state, implementing the 'MonadLogicState' interface.
newtype SolverT s m a = SolverT { unSolverT :: LogicT s (UnificationT m) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadLogic, MonadLogicCut)

instance MonadTrans (SolverT s) where
  lift = SolverT . lift . lift

instance Monad m => MonadUnification (SolverT s m) where
  fresh = SolverT $ lift fresh

instance (Monad m, SplittableState s) => MonadState s (SolverT s m) where
  state = SolverT . state

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
observeAllSolverT m s = runUnificationT $ observeAllLogicT (unSolverT m) s

-- | Like 'observeAllSolverT', but limits the number of results returned.
observeManySolverT :: (Monad m, SplittableState s) => Int -> SolverT s m a -> s -> m [a]
observeManySolverT n m s = runUnificationT $ observeManyLogicT n (unSolverT m) s

-- | This class encapsulates the algorithms required for proving each type of 'Goal'. The proof-
-- generating algorithm defined by 'prove' uses these functions to prove the goal specified by the
-- user and any sub-goal. Each algorithm has an associated "zero-overhead" version -- for example,
-- 'tryPredicate' and 'provePredicateWith'. These represent the minimal work needed to prove a
-- certain type of goal. But monads of this class can define more complex behavior; see the
-- "Control.Hspl.Internal.Debugger" for an example.
class (MonadUnification m, MonadLogicCut m) => MonadSolver m where
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
  tryPredicate :: Predicate -> HornClause -> m ProofResult
  -- | Attempt to prove a predicate using subsequent alternatives. 'retryPredicate' should have the
  -- same semantics as 'tryPredicate', modulo side-effects. The zero-overhead version is
  -- 'provePredicate'.
  retryPredicate :: Predicate -> HornClause -> m ProofResult
  -- | Attempt to prove that two terms can be unified. The resulting computation should either fail
  -- with 'mzero' or produce a unifier and a trivial proof of the unified terms. The zero-overhead
  -- version is 'proveUnifiable'.
  tryUnifiable :: TermEntry a => Term a -> Term a -> m ProofResult
  -- | Attempt to prove that two terms are identical. No new unifications are created. The resulting
  -- computation should either fail with 'mzero' or produce a trivial proof of the equality of the
  -- terms. The zero-overhead version is 'proveIdentical'.
  tryIdentical ::TermEntry a => Term a -> Term a -> m ProofResult
  -- | Attempt to prove equality of terms. The resulting computation should evaluate the right-hand
  -- side and, if successful, attempt to unify the resulting constant with the 'Term' on the left-
  -- hand side. If the right- hand side does not evaluate to a constant (for example, because it
  -- contains one or more free variables) the program should terminate with a runtime error as if by
  -- invoking 'errorUninstantiatedVariables'. The zero-overhead version is 'proveEqual'.
  tryEqual :: TermEntry a => Term a -> Term a -> m ProofResult
  -- | Attempt to prove one 'Term' is less than another. No new unifications are created. The
  -- resulting computation should evaluate both terms and, if successful, succeed if the evaluated
  -- left-hand side compares less than the evaluated right-hand side. If /either/ side does not
  -- evaluate to a constant, the program should terminate with a runtime error as if by invoking
  -- 'errorUninstantiatedVariables'. The zero-overhead version is 'proveLessThan'.
  tryLessThan :: (TermEntry a, Ord a) => Term a -> Term a -> m ProofResult
  -- | Attempt to prove the negation of a goal. No new unifications are created. The resulting
  -- computation should either fail with 'mzero' (if the negated goal succeeds at least once) or
  -- produce a trivial proof of the negation of the goal. The zero-overhead version is
  -- 'proveNot'.
  tryNot :: Goal -> m ProofResult
  -- | Attempt to prove the conjunction of two goals. The resulting computation should succeed,
  -- emitting a 'ProvedAnd' result with subproofs for each subgoal, if and only if both subgoals
  -- succeed. Further, it is important that unifications made while proving the left-hand side are
  -- applied to the right-hand side before proving it. The zero-overhead version is 'proveAnd'.
  tryAnd :: Goal -> Goal -> m ProofResult
  -- | Attempt to prove the first subgoal in a disjunction. The resulting computation should either
  -- fail with 'mzero', or emit a 'ProvedLeft' proof for each time the left subgoal succeeds. The
  -- zero-overhead version is 'proveOrLeft'.
  tryOrLeft :: Goal -> Goal -> m ProofResult
  -- | Attempt to prove the second subgoal in a disjunction. The resulting computaiton should have
  -- the same semantics as 'tryOr', modulo effects in the underlying monad and the fact that it
  -- emits 'provedRight' proofs rather than 'provedLeft' proofs. The zero-overhead version is
  -- 'proveOrRight'.
  tryOrRight :: Goal -> Goal -> m ProofResult
  -- | Emit a proof of 'Top'. This computation should always succeed with 'ProvedTop', perhaps after
  -- performing side-effects in the monad. The zero- overhead version is 'proveTop'.
  tryTop :: m ProofResult
  -- | Attempt to prove 'Bottom'. This computation should always fail with 'mzero', perhaps after
  -- performing effects in the monad. The zero-overhead version is 'proveBottom'.
  tryBottom :: m ProofResult
  -- | Attempt to prove an 'Alternatives' goal. In addition to any effects performed in the monad,
  -- this computation should have the following semantics:
  --
  --   1. Obtain all solutions of the inner goal, as if through 'runHspl'.
  --   2. For each solution, apply the unifier to the template 'Term' (first argument).
  --   3. Attempt to unify the resulting list with the output 'Term' (third argument).
  --
  -- The proof should succeed if and only if step 3 succeeds. In particular, note that the failure
  -- of the inner goal does not imply the failure of the proof. It should simply try to unify an
  -- empty list with the output term.
  --
  -- The zero-overhead version is 'proveAlternatives'.
  tryAlternatives :: TermEntry a => Term a -> Goal -> Term [a] -> m ProofResult
  -- | Attempt to prove a 'Once' goal. This computation should extract the first 'ProofResult' from
  -- the inner goal and return it. It should ignore any further solutions to the inner goal. The
  -- zero-overhead version is 'proveOnce'.
  tryOnce :: Goal -> m ProofResult
  -- | Computation to be invoked when a goal fails because there are no matching clauses. This
  -- computation should result in 'mzero', but may perform effects in the underlying monad first.
  failUnknownPred :: Predicate -> m ProofResult
  -- | Computation to be invoked when attempting to evaluate a 'Term' which contains ununified
  -- variables. As the type suggests, this should result in a call to 'error'.
  errorUninstantiatedVariables :: m a

instance Monad m => MonadSolver (SolverT s m) where
  tryPredicate = provePredicate
  retryPredicate = provePredicate
  tryUnifiable = proveUnifiable
  tryIdentical = proveIdentical
  tryEqual = proveEqual
  tryLessThan = proveLessThan
  tryNot = proveNot
  tryAnd = proveAnd
  tryOrLeft = proveOrLeft
  tryOrRight = proveOrRight
  tryTop = proveTop
  tryBottom = proveBottom
  tryAlternatives = proveAlternatives
  tryOnce = proveOnce
  failUnknownPred = const mzero
  errorUninstantiatedVariables = error "Variables are not sufficiently instantiated."

-- | Zero-overhead version of 'tryPredicate' and 'retryPredicate'.
provePredicate :: MonadSolver m => Predicate -> HornClause -> m ProofResult
provePredicate p c = do
  (g, u) <- getSubGoal p c
  case g of
    -- Exit early (without invoking any continuations) if the subgoal is Top. This isn't strictly
    -- necessary; if we were to invoke the continuation on Top it would just succeed immediately.
    -- But we want to give any observers the appearance of this goal succeeding immediately, with no
    -- further calls. It just makes the control flow a bit more intuitive (i.e. more similar to
    -- Prolog's)
    Top -> return (Resolved (unifyPredicate u p) ProvedTop, u)
    _ -> do (subProof, u') <- prove g
            let netU = u `compose` u'
            return (Resolved (unifyPredicate netU p) subProof, netU)
  where getSubGoal p' c' = do mg <- unify p' c'
                              case mg of
                                Just g -> return g
                                Nothing -> mzero

-- | Zero-overhead version of 'tryUnifiable'.
proveUnifiable :: (TermEntry a, MonadSolver m) => Term a -> Term a -> m ProofResult
proveUnifiable t1 t2 = case mgu t1 t2 of
  Just u -> return (Unified (unifyTerm u t1) (unifyTerm u t2), u)
  Nothing -> mzero

-- | Zero-overhead version of 'tryIdentical'.
proveIdentical :: (TermEntry a, MonadSolver m) => Term a -> Term a -> m ProofResult
proveIdentical t1 t2 = if t1 == t2
  then return (Identified t1 t2, mempty)
  else mzero

-- | Zero-overhead version of 'tryEqual'.
proveEqual :: (TermEntry a, MonadSolver m) => Term a -> Term a -> m ProofResult
proveEqual lhs rhs = do
  rhs' <- eval rhs
  case mgu lhs rhs' of
    Just u -> return (Equated (unifyTerm u lhs) (unifyTerm u rhs), u)
    Nothing -> mzero
  where eval t = case fromTerm t of
          Just t' -> return $ toTerm t'
          Nothing -> errorUninstantiatedVariables

-- | Zero-overhead version of 'tryLessThan'.
proveLessThan :: (TermEntry a, Ord a, MonadSolver m) => Term a -> Term a -> m ProofResult
proveLessThan lhs rhs = case (fromTerm lhs, fromTerm rhs) of
  (Just l, Just r) | l < r -> return (ProvedLessThan l r, mempty)
  (Just _, Just _) -> mzero
  _ -> errorUninstantiatedVariables

-- | Zero-overhead version of 'tryNot'.
proveNot :: MonadSolver m => Goal -> m ProofResult
proveNot g = lnot (prove g) >> return (Negated g, mempty)

-- | Zero-overhead version of 'tryAnd'.
proveAnd :: MonadSolver m => Goal -> Goal -> m ProofResult
proveAnd g1 g2 =
  do (proofLeft, uLeft) <- prove g1
     (proofRight, uRight) <- prove $ unifyGoal uLeft g2
     return (ProvedAnd proofLeft proofRight, uLeft `compose` uRight)

-- | Zero-overhead version of 'tryOrLeft'.
proveOrLeft :: MonadSolver m => Goal -> Goal -> m ProofResult
proveOrLeft g1 g2 =
  do (proof, u) <- prove g1
     return (ProvedLeft proof g2, u)

-- | Zero-overhead version of 'tryOrRight'.
proveOrRight :: MonadSolver m => Goal -> Goal -> m ProofResult
proveOrRight g1 g2 =
  do (proof, u) <- prove g2
     return (ProvedRight g1 proof, u)

-- | Zero-overhead version of 'tryTop'.
proveTop :: Monad m => m ProofResult
proveTop = return (ProvedTop, mempty)

-- | Zero-overhead version of 'tryBottom'.
proveBottom :: MonadSolver m => m ProofResult
proveBottom = mzero

-- | Zero-overhead version of 'tryAlternatives'.
proveAlternatives :: (MonadSolver m, TermEntry a) => Term a -> Goal -> Term [a] -> m ProofResult
proveAlternatives x g xs = do
  results <- getAlternatives $ prove g
  let (ps, us) = unzip results
  let alternatives = toTerm $ map (`unifyTerm` x) us
  let mu = mgu xs alternatives
  guard $ isJust mu
  let u = fromJust mu
  return (FoundAlternatives x g (unifyTerm u xs) ps, u)
  where getAlternatives m = do split <- msplit m
                               case split of
                                  Just (a, fk) -> (a:) `liftM` getAlternatives fk
                                  Nothing -> return []

-- | Zero-overhead version of 'tryOnce'.
proveOnce :: MonadSolver m => Goal -> m ProofResult
proveOnce g = do
  (p, u) <- once $ prove g
  return (ProvedOnce p, u)

-- | Produce a proof of the goal. This function will either fail, or backtrack over all possible
-- proofs. It will invoke the appropriate continuations in the given 'SolverCont' whenever a
-- relevant event occurs during the course of the proof.
prove :: MonadSolver m => Goal -> m ProofResult
prove g = case g of
  PredGoal p [] -> failUnknownPred p
  PredGoal p (c:cs) -> tryPredicate p c `mplus` msum (map (retryPredicate p) cs)
  CanUnify t1 t2 -> tryUnifiable t1 t2
  Identical t1 t2 -> tryIdentical t1 t2
  Equal t1 t2 -> tryEqual t1 t2
  LessThan t1 t2 -> tryLessThan t1 t2
  Not g' -> tryNot g'
  And g1 g2 -> tryAnd g1 g2
  Or g1 g2 -> tryOrLeft g1 g2 `mplus` tryOrRight g1 g2
  Top -> tryTop
  Bottom -> tryBottom
  Alternatives x g' xs -> tryAlternatives x g' xs
  Once g' -> tryOnce g'
