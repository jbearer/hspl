{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
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
  , solverCont
  , provePredicateWith
  , proveUnifiableWith
  , proveIdenticalWith
  , proveNotWith
  , proveEqualWith
  , proveWith
  , prove
  ) where

import Control.Monad.Identity
import Control.Monad.Logic
import Data.Data
import Data.Maybe
import Data.Monoid hiding (Sum, Product)

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Unification

-- | A resolution proof is a tree where each node is a 'Goal'. The root of the tree is the statement
-- to be proven. Each node follows logically from its children. A leaf, since it has no children,
-- stands on its own as a true statement -- in other words, leaves represent axioms.
data Proof = Axiom Goal | Proof Goal [Proof]
  deriving (Show, Eq)

-- | The output of the solver. This is meant to be treated as an opaque data type which can be
-- inspected via the functions defined in this module.
type ProofResult = (Proof, Unifier)

-- | Return the list of all goals or subgoals in the given result which unify with a particular goal.
searchProof :: ProofResult -> Predicate -> [Predicate]
searchProof (proof, _) = searchProof' proof
  where searchProof' pr g = case pr of
                              Proof (PredGoal p) ps -> [p | match p g] ++ recurse ps g
                              Proof _ ps -> recurse ps g
                              Axiom (PredGoal p) -> [p | match p g]
                              Axiom _ -> []
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
getSolution :: ProofResult -> Predicate
getSolution (proof, _) = case proof of
  Proof p _ -> getSol p
  Axiom p -> getSol p
  where getSol (PredGoal p) = p
        getSol _ = error "Top-level goal must be a predicate."

-- | Get the set of theorems which were proven by each 'Proof' tree in a forest.
getAllSolutions :: [ProofResult] -> [Predicate]
getAllSolutions = map getSolution

-- | Attempt to prove the given predicate from the clauses in the given 'Program'. This function
-- returns a forest of 'Proof' trees. If the goal cannot be derived from the given clauses, the
-- result is @[]@. Otherwise, the contents of the resulting list represent various alternative ways
-- of proving the theorem. If there are variables in the goal, they may unify with different values
-- in each alternative proof.
runHspl :: Program -> Predicate -> [ProofResult]
runHspl p g = observeAllSolver $ prove p (PredGoal g)

-- | Like 'runHspl', but return at most the given number of proofs.
runHsplN :: Int -> Program -> Predicate -> [ProofResult]
runHsplN n p g = observeManySolver n $ prove p (PredGoal g)

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
The basic algorithm is fairly simple. We maintain a set of goals which need to be proven. Initially,
this set consists only of the client's input goal. While the set is not empty, we remove a goal and
find all clauses in the program whose positive literal is the same predicate (name and type) as the
current goal. For each such alternative, we attempt to unify the goal with the positive literal. If
unification succeeds, we apply the unifier to each of the negative literals of the clause and add
these literals to the set of goals. If unification fails or if there are no matching clauses, the
goal fails and we backtrack until we reach a choice point, at which we try the next alternative
goal. If a goal fails and all choice-points have been exhaustively tried, then the whole proof
fails. If a goal succeeds and there are untried choice-points, we backtrack and generate additional
proofs if possible.

Non-predicate goals have different semantics. For 'CanUnify' goals, instead of looking for matching
clauses and adding new subgoals, we simply try to find a unifier for the relevant terms and succeed
or fail accordingly.

There is an additional layer of complexity here. We do not proceed from one step of the algorithm to
the next directly. Instead, at each intermediate step, we invoke one of the continuation functions
defined in 'SolverCont'. With the right choice of continuations (see 'solverCont') we can move from
one step to the next seamlessly, running the basic algorithm with no overhead. However, these
continuations make it possible to hook additional behavior into crucial events in the algorithm,
which make possible things like the interactive debugger in "Control.Hspl.Internal.Debugger".
-}

-- | Unified structure containing all of the continuations which may be invoked by the prover
-- algorithm.
data SolverCont (m :: * -> *) =
  SolverCont {
               -- | Continuation to be invoked when attempting to prove a predicate using the first
               -- alternative (the first 'HornClause' with a matching positive literal). The
               -- resulting computation in the 'SolverT' monad should either fail with 'mzero' or
               -- produce a proof of the predicate. The zero-overhead version of this continuation
               -- is 'provePredicateWith'.
               tryPredicate :: Predicate -> HornClause -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove a predicate using subsequent
               -- alternatives. This continuation should have the same semantics as 'tryPredicate',
               -- modulo effects in the underlying monad. The zero-overhead version of this
               -- continuation is 'provePredicateWith'.
             , retryPredicate :: Predicate -> HornClause -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove that two terms can be
               -- unified. The resulting computation in the 'SolverT' monad should either fail with
               -- 'mzero' or produce a unifier and a trivial proof of the unified terms. The zero-
               -- overhead version of this continuation is 'proveUnifiableWith'.
             , tryUnifiable :: forall a. Typeable a => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove that two terms are identical
               -- after applying the current unifier. No new unifications are created. The resulting
               -- computation in the 'SolverT' monad should either fail with 'mzero' or produce a
               -- trivial proof of the equality of the terms. The zero-overhead version of this
               -- continuation is 'proveIdenticalWith'.
             , tryIdentical :: forall a. Typeable a => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove the negation of a goal. No
               -- new unifications are created. The resulting computation in the 'SolverT' monad
               -- should either fail with 'mzero' (if the negated goal succeeds at least once) or
               -- produce a trivial proof of the negation of the goal. The zero-overhead version of
               -- this continuation is 'proveNotWith'.
             , tryNot :: Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove equality of arithmetic
               -- expressions. The resulting computation in the 'SolverT' monad should evaluate the
               -- right-hand side as an arithmetic expression and, if successful, attempt to unify
               -- the resulting constant with the 'Term' on the left-hand side. If the right-hand
               -- side does not evaluate to a constant (for example, because it contains one or more
               -- free variables) the program should terminate with a runtime error. The zero-
               -- overhead version of this continuation is 'proveEqualWith'.
             , tryEqual :: forall a. ( Typeable a
                                     , Data a
                                     , Eq a
#ifdef SHOW_TERMS
                                     , Show a
#endif
                                     ) => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when a goal fails because there are no matching
               -- clauses. This computation should result in 'mzero', but may perform effects in the
               -- underlying monad first.
             , errorUnknownPred :: Predicate -> SolverT m ProofResult
             }

-- | Continuations which, when passed to 'proveWith', will allow statements in the given program to
-- be proven with no additional behavior and no interprative overhead.
solverCont :: Program -> SolverCont Identity
solverCont p = SolverCont { tryPredicate = provePredicateWith (solverCont p) p
                          , retryPredicate = provePredicateWith (solverCont p) p
                          , tryUnifiable = proveUnifiableWith (solverCont p) p
                          , tryIdentical = proveIdenticalWith (solverCont p) p
                          , tryNot = proveNotWith (solverCont p) p
                          , tryEqual = proveEqualWith (solverCont p) p
                          , errorUnknownPred = const mzero
                          }

-- | Run the minimal, zero-overhead version of the algorithm by supplying the appropriate
-- continuations to 'proveWith'.
prove :: Program -> Goal -> Solver ProofResult
prove p = proveWith (solverCont p) p

-- | Produce a proof of the predicate from the given 'HornClause'. The clause's positive literal
-- should match with the predicate; that is, it should have the same name and type. If the positive
-- literal also unifies with the predicate, then the unifier is applied to each negative literal,
-- and each unified negative literal is proven as a subgoal using the given continuations.
provePredicateWith :: Monad m =>
                      SolverCont m -> Program -> Predicate -> HornClause -> SolverT m ProofResult
provePredicateWith cont program p c = do
  (gs, u) <- getSubGoals p c
  case gs of
    [] -> return (Axiom $ unifyGoal u (PredGoal p), u)
    _ -> do (subProofs, netU) <- proveSubGoals mempty gs
            return (Proof (unifyGoal netU (PredGoal p)) subProofs, netU)
  where getSubGoals p' c' = do mgs <- lift $ unify p' c'
                               case mgs of
                                 Just gs -> return gs
                                 Nothing -> mzero
        proveSubGoals u [] = return ([], u)
        proveSubGoals u (g:gs) = do let g' = unifyGoal u g
                                    (proof, u') <- proveWith cont program g'
                                    (proofs, u'') <- proveSubGoals (u <> u') gs
                                    return (proof:proofs, u'')

-- | Check if the given terms can unify. If so, produce the unifier and a trivial proof of their
-- unifiability. Use the given continuations when proving subgoals.
proveUnifiableWith :: (Typeable a, Monad m) =>
                      SolverCont m -> Program -> Term a -> Term a -> SolverT m ProofResult
proveUnifiableWith _ _ t1 t2 = case mgu t1 t2 of
  Just u -> return (Axiom $ unifyGoal u $ CanUnify t1 t2, u)
  Nothing -> mzero

-- | Check if the given terms are identical (i.e. they have already been unified). If so, produce a
-- trivial proof of their equality. Use the given continuations when proving subgoals.
proveIdenticalWith :: (Typeable a, Monad m) =>
                      SolverCont m -> Program -> Term a -> Term a -> SolverT m ProofResult
proveIdenticalWith _ _ t1 t2 = if t1 == t2
  then return (Axiom $ Identical t1 t2, mempty)
  else mzero

-- | Succeed if and only if the given 'Goal' fails. No new bindings are created in the process.
proveNotWith :: Monad m => SolverCont m -> Program -> Goal -> SolverT m ProofResult
proveNotWith cont program g = ifte (once $ proveWith cont program g)
                                   (const mzero)
                                   (return (Axiom $ Not g, mempty))

-- | Check if the value of the right-hand side unifies with the left-hand side.
proveEqualWith :: ( Typeable a
                  , Data a
                  , Eq a
#ifdef SHOW_TERMS
                  , Show a
#endif
                  , Monad m
                  ) =>
                  SolverCont m -> Program -> Term a -> Term a -> SolverT m ProofResult
proveEqualWith _ _ lhs rhs = case mgu lhs (Constant $ eval rhs) of
    Just u -> return (Axiom $ Equal (unifyTerm u lhs) (unifyTerm u rhs), u)
    Nothing -> mzero
  where eval (Constant c) = c
        eval (Sum t1 t2) = eval t1 + eval t2
        eval (Difference t1 t2) = eval t1 - eval t2
        eval (Product t1 t2) = eval t1 * eval t2
        eval (Quotient t1 t2) = eval t1 / eval t2
        eval (IntQuotient t1 t2) = eval t1 `div` eval t2
        eval (Modulus t1 t2) = eval t1 `mod` eval t2
        eval (Variable _) = error "Arguments are not sufficiently instantiated."
        eval _ = error "Argument must be an arithmetic expression."

-- | Produce a proof of the goal from the clauses in the program. This function will either fail,
-- or backtrack over all possible proofs. It will invoke the appropriate continuations in the given
-- 'SolverCont' whenever a relevant event occurs during the course of the proof.
proveWith :: Monad m => SolverCont m -> Program -> Goal -> SolverT m ProofResult
proveWith cont program g = case g of
  PredGoal p -> case findClauses p program of
    [] -> errorUnknownPred cont p
    c:cs -> tryPredicate cont p c `mplus` msum (map (retryPredicate cont p) cs)
  CanUnify t1 t2 -> tryUnifiable cont t1 t2
  Identical t1 t2 -> tryIdentical cont t1 t2
  Not g' -> tryNot cont g'
  Equal t1 t2 -> tryEqual cont t1 t2
