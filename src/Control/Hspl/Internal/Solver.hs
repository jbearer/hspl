{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
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
  , proveEqualWith
  , proveLessThanWith
  , proveNotWith
  , proveAndWith
  , proveOrLeftWith
  , proveOrRightWith
  , proveTopWith
  , proveBottomWith
  , proveAlternativesWith
  , proveOnceWith
  , proveWith
  , prove
  ) where

import Control.Monad.Identity
import Control.Monad.Logic
import Data.Data
import Data.Maybe
import Data.Monoid hiding (Sum, Product)

import Control.Hspl.Internal.Ast
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
runHspl = observeAllSolver . prove

-- | Like 'runHspl', but return at most the given number of proofs.
runHsplN :: Int -> Goal -> [ProofResult]
runHsplN n = observeManySolver n . prove

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
unification succeeds, we apply the unifier to the negative literal of the clause and add that
literal to the set of goals. If unification fails or if there are no matching clauses, the goal
fails and we backtrack until we reach a choice point, at which we try the next alternative goal. If
a goal fails and all choice-points have been exhaustively tried, then the whole proof fails. If a
goal succeeds and there are untried choice-points, we backtrack and generate additional proofs if
possible.

Non-predicate goals have different semantics:

* For 'CanUnify' goals, instead of looking for matching clauses and adding new subgoals, we simply
  try to find a unifier for the relevant terms and succeed or fail accordingly.
* For 'Identical' goals, we compare the terms using the '==' operator for 'Term' and succeed or fail
  if the result is 'True' or 'False', respectively.
* For 'Equal' goals, we evaluate the right-hand side using 'fromTerm'. If that succeeds, we convert
  the now-simplified constant back to its abstract 'Term' representation using 'toTerm', and then
  attempt to unify that 'Term' with the left-hand side.
* For 'LessThan' goals, we evaluate both sides and compare the results using '<'.
* For 'Not' goals, we attempt to prove the negated goal, and fail if the inner proof succeeds or
  vice versa.
* For 'And' goals, we first attempt to prove the left-hand side. If that succeeds, we apply the
  resulting unifier to the right-hand side and then attempt to prove the unified goal.
* For 'Or' goals, we introduce a choice-point and nondeterministically attempt to prove both
  subgoals. If either subgoal succeeds, the proof will succeed at least once. If both succeed, the
  prover will backtrack over both possible alternatives, succeeding once for each time either
  subgoal suceeds.
* For 'Top', we simply emit a trivial proof with an empty 'Unifier'.
* For 'Bottom', we immediately fail.

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
             , tryUnifiable :: forall a. TermEntry a => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove that two terms are identical
               -- after applying the current unifier. No new unifications are created. The resulting
               -- computation in the 'SolverT' monad should either fail with 'mzero' or produce a
               -- trivial proof of the equality of the terms. The zero-overhead version of this
               -- continuation is 'proveIdenticalWith'.
             , tryIdentical :: forall a. TermEntry a => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove equality of terms. The
               -- resulting computation in the 'SolverT' monad should evaluate the right-hand side
               -- and, if successful, attempt to unify the resulting constant with the 'Term' on the
               -- left-hand side. If the right-hand side does not evaluate to a constant (for
               -- example, because it contains one or more free variables) the program should
               -- terminate with a runtime error. The zero-overhead version of this continuation is
               -- 'proveEqualWith'.
             , tryEqual :: forall a. TermEntry a => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove one 'Term' is less than
               -- another. No new unifications are created. The resulting computation in the
               -- 'SolverT' monad should evaluate both terms and, if successful, succeed if the
               -- evaluated left-hand side compares less than the evaluated right-hand side. If
               -- /either/ side does not evaluate to a constant, the program should terminate with a
               -- runtime error. The zero-overhead version of this continuation is
               -- 'proveLessThanWith'.
             , tryLessThan :: forall a. (TermEntry a, Ord a) => Term a -> Term a -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove the negation of a goal. No
               -- new unifications are created. The resulting computation in the 'SolverT' monad
               -- should either fail with 'mzero' (if the negated goal succeeds at least once) or
               -- produce a trivial proof of the negation of the goal. The zero-overhead version of
               -- this continuation is 'proveNotWith'.
             , tryNot :: Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove the conjunction of two
               -- goals. The resulting computation in the 'SolverT' monad should succeed, emitting a
               -- 'ProvedAnd' result with subproofs for each subgoal, if and only if both subgoals
               -- succeed. Further, it is important that unifications made while proving the left-
               -- hand side are applied to the right-hand side before proving it. The zero-overhead
               -- version of this continuation is 'proveAndWith'.
             , tryAnd :: Goal -> Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove the first subgoal in a
               -- disjunction. The resulting computation in the 'SolverT' monad should either fail
               -- with 'mzero', or emit 'ProvedLeft' and 'ProvedRight' proofs for each time the left
               -- and right subgoals succeed, respectively. The zero-overhead version of this
               -- continuation is 'proveOrLeftWith'.
             , tryOrLeft :: Goal -> Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove the second subgoal in a
               -- disjunction. This continuation should have the same semantics as 'tryOr', modulo
               -- effects in the underlying monad. The zero-overhead version of this continuation is
               -- 'proveOrRightWith'.
             , tryOrRight :: Goal -> Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove 'Top'. This continuation
               -- should always succeed with 'ProvedTop', perhaps after performing effects in the
               -- underlying monad. The zero-overhead version of this continuation is
               -- 'proveTopWith'.
             , tryTop :: SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove 'Bottom'. This continuation
               -- should always fail with 'mzero', perhaps after performing effects in the
               -- underlying monad. The zero-overhead version of this continuation is
               -- 'proveBottomWith'.
             , tryBottom :: SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove an 'Alternatives' goal. In
               -- addition to any effects performed in the underlying monad, this continuation
               -- should have the following semantics:
               --
               --   1. Obtain all solutions of the inner goal, as if through 'runHspl'.
               --   2. For each solution, apply the unifier to the template 'Term' (first argument).
               --   3. Attempt to unify the resulting list with the output 'Term' (third argument).
               --
               -- The proof should succeed if and only if step 3. succeeds. In particular, note that
               -- the failure of the inner goal does not imply the failure of the proof. It should
               -- simply try to unify an empty list with the output term.
               --
               -- The zero-overhead version of this continuation is 'proveAlternativesWith'.
             , tryAlternatives :: forall a. TermEntry a =>
                                  Term a -> Goal -> Term [a] -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to prove a 'Once' goal'. This
               -- continuation should extract the first 'ProofResult' from the inner goal using, for
               -- example, 'proveWith', and return it. It should ignore any further solutions to the
               -- inner goal. The zero-overhead version of this continuation is 'proveOnceWith'.
             , tryOnce :: Goal -> SolverT m ProofResult
               -- | Continuation to be invoked when a goal fails because there are no matching
               -- clauses. This computation should result in 'mzero', but may perform effects in the
               -- underlying monad first.
             , failUnknownPred :: Predicate -> SolverT m ProofResult
               -- | Continuation to be invoked when attempting to evaluate a 'Term' which contains
               -- ununified variables. This is a runtime error.
             , errorUninstantiatedVariables :: forall a. a
             }

-- | Continuations which, when passed to 'proveWith', will allow statements to be proven with no
-- additional behavior and no interprative overhead.
solverCont :: SolverCont Identity
solverCont = SolverCont { tryPredicate = provePredicateWith solverCont
                        , retryPredicate = provePredicateWith solverCont
                        , tryUnifiable = proveUnifiableWith solverCont
                        , tryIdentical = proveIdenticalWith solverCont
                        , tryEqual = proveEqualWith solverCont
                        , tryLessThan = proveLessThanWith solverCont
                        , tryNot = proveNotWith solverCont
                        , tryAnd = proveAndWith solverCont
                        , tryOrLeft = proveOrLeftWith solverCont
                        , tryOrRight = proveOrRightWith solverCont
                        , tryTop = proveTopWith solverCont
                        , tryBottom = proveBottomWith solverCont
                        , tryAlternatives = proveAlternativesWith solverCont
                        , tryOnce = proveOnceWith solverCont
                        , failUnknownPred = const mzero
                        , errorUninstantiatedVariables =
                            error "Variables are not sufficiently instantiated."
                        }

-- | Run the minimal, zero-overhead version of the algorithm by supplying the appropriate
-- continuations to 'proveWith'.
prove :: Goal -> Solver ProofResult
prove = proveWith solverCont

-- | Produce a proof of the predicate from the given 'HornClause'. The clause's positive literal
-- should match with the predicate; that is, it should have the same name and type. If the positive
-- literal also unifies with the predicate, then the unifier is applied to each negative literal,
-- and each unified negative literal is proven as a subgoal using the given continuations.
provePredicateWith :: Monad m => SolverCont m -> Predicate -> HornClause -> SolverT m ProofResult
provePredicateWith cont p c = do
  (g, u) <- getSubGoal p c
  case g of
    -- Exit early (without invoking any continuations) if the subgoal is Top. This isn't strictly
    -- necessary; if we were to invoke the continuation on Top it would just succeed immediately.
    -- But we want to give any observers the appearance of this goal succeeding immediately, with no
    -- further calls. It just makes the control flow a bit more intuitive (i.e. more similar to
    -- Prolog's)
    Top -> return (Resolved (unifyPredicate u p) ProvedTop, u)
    _ -> do (subProof, u') <- proveWith cont g
            let netU = u <> u'
            return (Resolved (unifyPredicate netU p) subProof, netU)
  where getSubGoal p' c' = do mg <- lift $ unify p' c'
                              case mg of
                                Just g -> return g
                                Nothing -> mzero

-- | Check if the given terms can unify. If so, produce the unifier and a trivial proof of their
-- unifiability. Use the given continuations when proving subgoals.
proveUnifiableWith :: (TermEntry a, Monad m) =>
                      SolverCont m -> Term a -> Term a -> SolverT m ProofResult
proveUnifiableWith _ t1 t2 = case mgu t1 t2 of
  Just u -> return (Unified (unifyTerm u t1) (unifyTerm u t2), u)
  Nothing -> mzero

-- | Check if the given terms are identical (i.e. they have already been unified). If so, produce a
-- trivial proof of their equality. Use the given continuations when proving subgoals.
proveIdenticalWith :: (TermEntry a, Monad m) =>
                      SolverCont m -> Term a -> Term a -> SolverT m ProofResult
proveIdenticalWith _ t1 t2 = if t1 == t2
  then return (Identified t1 t2, mempty)
  else mzero

-- | Check if the value of the right-hand side unifies with the left-hand side.
proveEqualWith :: (TermEntry a, Monad m) =>
                  SolverCont m -> Term a -> Term a -> SolverT m ProofResult
proveEqualWith cont lhs rhs = case mgu lhs (eval rhs) of
    Just u -> return (Equated (unifyTerm u lhs) (unifyTerm u rhs), u)
    Nothing -> mzero
  where eval :: TermEntry a => Term a -> Term a
        eval t = case fromTerm t of
          Just t' -> toTerm t'
          Nothing -> errorUninstantiatedVariables cont

-- | Check if the left-hand side is less than the right-hand side. No new bindings are created.
proveLessThanWith :: (TermEntry a, Ord a, Monad m) =>
                     SolverCont m -> Term a -> Term a -> SolverT m ProofResult
proveLessThanWith cont lhs rhs = case (fromTerm lhs, fromTerm rhs) of
  (Just l, Just r) | l < r -> return (ProvedLessThan l r, mempty)
  (Just _, Just _) -> mzero
  _ -> errorUninstantiatedVariables cont

-- | Succeed if and only if the given 'Goal' fails. No new bindings are created in the process.
proveNotWith :: Monad m => SolverCont m -> Goal -> SolverT m ProofResult
proveNotWith cont g = ifte (once $ proveWith cont g)
                           (const mzero)
                           (return (Negated g, mempty))

-- | Succeed if and only if both goals succeed in sequence. Unifications made while proving the
-- first goal will be applied to the second goal before proving it.
proveAndWith :: Monad m => SolverCont m -> Goal -> Goal -> SolverT m ProofResult
proveAndWith cont g1 g2 =
  do (proofLeft, uLeft) <- proveWith cont g1
     (proofRight, uRight) <- proveWith cont $ unifyGoal uLeft g2
     return (ProvedAnd proofLeft proofRight, uLeft <> uRight)

-- | Succeed if and only if the first of the given 'Goal's succeeds.
proveOrLeftWith :: Monad m => SolverCont m -> Goal -> Goal -> SolverT m ProofResult
proveOrLeftWith cont g1 g2 =
  do (proof, u) <- proveWith cont g1
     return (ProvedLeft proof g2, u)

-- | Succeed if and only if the second of the given 'Goal's succeeds.
proveOrRightWith :: Monad m => SolverCont m -> Goal -> Goal -> SolverT m ProofResult
proveOrRightWith cont g1 g2 =
  do (proof, u) <- proveWith cont g2
     return (ProvedRight g1 proof, u)

-- | Always succeed, creating no new bindings.
proveTopWith :: Monad m => SolverCont m -> SolverT m ProofResult
proveTopWith _ = return (ProvedTop, mempty)

-- | Always fail.
proveBottomWith :: Monad m => SolverCont m -> SolverT m ProofResult
proveBottomWith _ = mzero

-- | Succeed if and only if the list term unifies with the alternatives of the template term when
-- proving the given goal.
proveAlternativesWith :: (Monad m, TermEntry a) =>
                         SolverCont m -> Term a -> Goal -> Term [a] -> SolverT m ProofResult
proveAlternativesWith cont x g xs = do
  results <- solverLift $ observeAllSolverT $ proveWith cont g
  let (ps, us) = unzip results
  let alternatives = toTerm $ map (`unifyTerm` x) us
  let mu = mgu xs alternatives
  guard $ isJust mu
  let u = fromJust mu
  return (FoundAlternatives x g (unifyTerm u xs) ps, u)

-- | Produce at most one proof of the inner goal.
proveOnceWith :: Monad m => SolverCont m -> Goal -> SolverT m ProofResult
proveOnceWith cont g = do
  (p, u) <- once $ proveWith cont g
  return (ProvedOnce p, u)

-- | Produce a proof of the goal. This function will either fail, or backtrack over all possible
-- proofs. It will invoke the appropriate continuations in the given 'SolverCont' whenever a
-- relevant event occurs during the course of the proof.
proveWith :: Monad m => SolverCont m -> Goal -> SolverT m ProofResult
proveWith cont g = case g of
  PredGoal p [] -> failUnknownPred cont p
  PredGoal p (c:cs) -> tryPredicate cont p c `mplus` msum (map (retryPredicate cont p) cs)
  CanUnify t1 t2 -> tryUnifiable cont t1 t2
  Identical t1 t2 -> tryIdentical cont t1 t2
  Equal t1 t2 -> tryEqual cont t1 t2
  LessThan t1 t2 -> tryLessThan cont t1 t2
  Not g' -> tryNot cont g'
  And g1 g2 -> tryAnd cont g1 g2
  Or g1 g2 -> tryOrLeft cont g1 g2 `mplus` tryOrRight cont g1 g2
  Top -> tryTop cont
  Bottom -> tryBottom cont
  Alternatives x g' xs -> tryAlternatives cont x g' xs
  Once g' -> tryOnce cont g'
