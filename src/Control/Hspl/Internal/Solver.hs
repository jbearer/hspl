{-# LANGUAGE KindSignatures #-}
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
    Goal
  , Proof (..)
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
  , Solver
  , SolverT
  , solverLift
  , observeAllSolver
  , observeManySolver
  , observeAllSolverT
  , observeManySolverT
  -- ** The proof-generating algorithm
  -- $prover
  , SolverCont (..)
  , getMatchingClause
  , getSubGoals
  , proveWith
  , prove
  ) where

import Control.Monad.Identity
import Control.Monad.Logic
import Data.Maybe
import Data.Typeable

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Unification

-- | The statement that the solver is trying to prove. The solver will prove many goals in the
-- course of a single proof, as each goal in turn follows from some number of subgoals.
type Goal = Predicate

-- | A resolution proof is a tree where each node is a goal (a 'Predicate'). The root of the tree is
-- the statement to be proven. Each node follows logically from its children. A leaf, since it has
-- no children, stands on its own as a true statement -- in other words, leaves represent axioms.
data Proof = Axiom Predicate | Proof Predicate [Proof]
  deriving (Show, Eq)

-- | The output of the solver. This is meant to be treated as an opaque data type which can be
-- inspected via the functions defined in this module.
type ProofResult = (Proof, Unifier)

-- | Return the list of all goals or subgoals in the given result which unify with a particular goal.
searchProof :: ProofResult -> Goal -> [Goal]
searchProof (proof, _) = searchProof' proof
  where searchProof' pr g = case pr of
                              Proof p ps -> [p | match p g] ++ recurse ps g
                              Axiom p -> [p | match p g]
        recurse ps g' = concatMap (\p' -> searchProof' p' g') ps
        match (Predicate name arg) (Predicate name' arg')
          | name == name' = isJust $ cast arg >>= mgu arg'
          | otherwise = False

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

-- | Get the theorem which follows from a 'Proof'. This will always be the predicate at the root of a
-- proof tree.
getSolution :: ProofResult -> Goal
getSolution (Proof p _, _) = p
getSolution (Axiom p, _) = p

-- | Get the set of theorems which were proven by each 'Proof' tree in a forest.
getAllSolutions :: [ProofResult] -> [Goal]
getAllSolutions = map getSolution

-- | Attempt to prove the given predicate from the clauses in the given 'Program'. This function
-- returns a forest of 'Proof' trees. If the goal cannot be derived from the given clauses, the
-- result is @[]@. Otherwise, the contents of the resulting list represent various alternative ways
-- of proving the theorem. If there are variables in the goal, they may unify with different values
-- in each alternative proof.
runHspl :: Program -> Goal -> [ProofResult]
runHspl p g = observeAllSolver $ prove p g

-- | Like 'runHspl', but return at most the given number of proofs.
runHsplN :: Int -> Program -> Goal -> [ProofResult]
runHsplN n p g = observeManySolver n $ prove p g

-- | The monad which defines the backtracking control flow of the solver.
type SolverT m = LogicT (UnificationT m)

-- | A non-transformer version of 'SolverT'.
type Solver = SolverT Identity

-- | Get all results from a 'Solver' computation.
observeAllSolver :: Solver a -> [a]
observeAllSolver = runUnification . observeAllT

-- | Get the specified number of results from a 'Solver' computation.
observeManySolver :: Int -> Solver a -> [a]
observeManySolver n = runUnification . observeManyT n

-- | Run a 'SolverT' transformed computation, and return a computation in the underlying monad for
-- each solution to the logic computation.
observeAllSolverT :: Monad m => SolverT m a -> m [a]
observeAllSolverT = runUnificationT . observeAllT

-- | Like 'observeAllSolverT', but limits the number of results returned.
observeManySolverT :: Monad m => Int -> SolverT m a -> m [a]
observeManySolverT n = runUnificationT . observeManyT n

-- | Lift a computation in the underlying monad into the transformed 'SolverT' monad.
solverLift :: Monad m => m a -> SolverT m a
solverLift = lift . lift

{- $prover
The basic algorithm is fairly simple. We maintain a set of goals which need to be proven.
Initially, this set consists only of the client's input goal. While the set is not empty, we
remove a goal and find all clauses in the program whose positive literal is the same predicate
(name and type) as the current goal. For each such alternative, we attempt to unify the goal
with the positive literal. If unification succeeds, we apply the unifier to each of the
negative literals of the clause and add these literals to the set of goals. If unification
fails or if there are no matching clauses, the goal fails and we backtrack until we reach a
choice point, at which we try the next alternative goal. If a goal fails and all choice-points
have been exhaustively tried, then the whole proof fails. If a goal succeeds and there are
untried choice-points, we backtrack and generate additional proofs if possible.

There is an additional layer of complexity here. We do not proceed from one step of the
algorithm to the next directly. Instead, at each intermediate step, we invoke one of the
continuation functions defined in 'SolverCont'. With the right choice of continuations (see
'prove') we can move from one step to the next seamlessly, running the basic algorithm with no
overhead. However, these continuations make it possible to hook additional behavior into
crucial events in the algorithm, which make possible things like the interactive debugger in
"Control.Hspl.Internal.Debugger".
-}

-- | Unified structure containing all of the continuations which may be invoked by the prover
-- algorithm.
data SolverCont (m :: * -> *) =
  SolverCont {
               -- | Continuation to be invoked when a new goal or subgoal is encountered. This
               -- function should return a computation which generates proofs of the goal. To run
               -- the zero-overhead version of the algorithm, use 'prove'.
               beginGoal :: Program -> Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when trying the first clause whose positive literal
               -- matches the current goal. This function should return a computation which yields
               -- the clause to be tried. Usually, this can just be 'return'.
             , firstAlternative :: HornClause -> SolverT m HornClause
               -- | Continuation to be invoked when trying additional matching clauses. The zero-
               -- overhead version is 'return'.
             , nextAlternative :: HornClause -> SolverT m HornClause
               -- | Continuation to be invoked when a goal fails because there are not matching
               -- clauses. This computation should result in 'mzero', but may perform effects in the
               -- underlying monad first.
             , failUnknownPred :: SolverT m HornClause
               -- | Continuation to be invoked when a goal fails because it did not unify with the
               -- current alternative. This computation should result in 'mzero', but may perform
               -- effects in the underlying monad first.
             , failUnification :: SolverT m ([Goal], Unifier)
               -- | Continuation to be invoked when a goal succeeds. This function should return a
               -- computation which yields the generated proof. Usually, this can just be 'return'.
             , exit :: ProofResult -> SolverT m ProofResult
             }

-- | Run the minimal, zero-overhead version of the algorithm by supplying the appropriate
-- continuations to 'proveWith'.
prove :: Program -> Goal -> Solver ProofResult
prove = proveWith SolverCont { beginGoal = prove
                             , firstAlternative = return
                             , nextAlternative = return
                             , failUnknownPred = mzero
                             , failUnification = mzero
                             , exit = return
                             }


-- | Nondeterminstically choose a clause with a literal which clashes with the given goal. In other
-- words, select a clause whose positive literal is an application of the same predicate as the
-- goal. This function outputs a disjunction of clauses in the 'Solver' monad, and so subsequent
-- computations will backtrack over all matching clauses.
--
-- If there are no matching clauses, this function will invoke the 'failUnknownPred' continuation
-- in the given 'SolverCont'. Otherwise, it will invoke 'firstAlternative' for the first matching
-- clause and 'nextAlternative' for each additional match.
getMatchingClause :: Monad m => SolverCont m -> Program -> Goal -> SolverT m HornClause
getMatchingClause cont p g = case findClauses g p of
  [] -> failUnknownPred cont
  c:cs -> firstAlternative cont c `mplus` msum (map (nextAlternative cont) cs)

-- | Attempt to unify the goal with the positive literal of the given clause and return the
-- resulting subgoals. The subgoals are the negative literals of the clause after applying the
-- unifier.
--
-- If unification succeeds, this function simply returns the resulting subgoals. Otherwise, it will
-- invoke the 'failUnification' continuation in the given 'SolverCont'.
getSubGoals :: Monad m => SolverCont m -> Goal -> HornClause -> SolverT m ([Goal], Unifier)
getSubGoals cont g c = do
  mgs <- lift $ unifyGoal g c
  case mgs of
    Just gs -> return gs
    Nothing -> failUnification cont

-- | Produce a proof of the goal from the clauses in the program. This function will either fail,
-- or backtrack over all possible proofs. It will invoke the appropriate continuations in the given
-- 'SolverCont' whenever a relevant event occurs during the course of the proof.
proveWith :: Monad m => SolverCont m -> Program -> Goal -> SolverT m ProofResult
proveWith cont p g = do
  c <- getMatchingClause cont p g
  (gs, u) <- getSubGoals cont g c
  case gs of
    [] -> do let unifiedGoal = unifyPredicate u g
             exit cont (Axiom unifiedGoal, u)
    _ -> do subs <- forM gs (beginGoal cont p)
            let (subProofs, subUs) = unzip subs
            let netU = netUnifier $ u : subUs
            let unifiedGoal = unifyPredicate netU g
            exit cont (Proof unifiedGoal subProofs, netU)
