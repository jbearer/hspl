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
  -- * Solver
  , Solver
  , runHspl
  , runHsplN
  , getMatchingClause
  , getSubGoals
  , prove
  ) where

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

-- | The monad which defines the backtracking control flow of the solver.
type Solver = LogicT Unification

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
runHspl p g = runUnification $ observeAllT $ prove p g

-- | Like 'runHspl', but return at most the given number of proofs.
runHsplN :: Int -> Program -> Goal -> [ProofResult]
runHsplN n p g = runUnification $ observeManyT n $ prove p g

-- | Nondeterminstically choose a clause with a literal which clashes with the given goal. In other
-- words, select a clause whose positive literal is an application of the same predicate as the
-- goal. This function outputs clauses in the 'Solver' monad, and so subsequent computations will
-- backtrack over all matching clauses.
getMatchingClause :: Program -> Goal -> Solver HornClause
getMatchingClause p g = msum $ map return $ findClauses g p

-- | Attempt to unify the goal with the positive literal of the given clause and return the
-- resulting subgoals. The subgoals are the negative literals of the clause after applying the
-- unifier. This function will either fail or produce exactly one set of subgoals.
getSubGoals :: Goal -> HornClause -> Solver ([Goal], Unifier)
getSubGoals g c = do
  mgs <- lift $ unifyGoal g c
  case mgs of
    Just gs -> return gs
    Nothing -> mzero

-- | Produce a proof of the goal from the clauses in the program. This function will either fail,
-- or backtrack over all possible proofs.
prove :: Program -> Goal -> Solver ProofResult
prove p g = do
  c <- getMatchingClause p g
  (gs, u) <- getSubGoals g c
  case gs of
    [] -> do let unifiedGoal = unifyPredicate u g
             return (Axiom unifiedGoal, u)
    _ -> do subs <- forM gs (prove p)
            let (subProofs, subUs) = unzip subs
            let netU = netUnifier $ u : subUs
            let unifiedGoal = unifyPredicate netU g
            return (Proof unifiedGoal subProofs, netU)
