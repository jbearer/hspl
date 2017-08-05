{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraints
{-# LANGUAGE TypeSynonymInstances #-}

module SolverTest where

import Testing
import Control.DeepSeq (NFData (..))
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.Unification hiding (Unified)
import qualified Control.Hspl.Internal.Unification as U
import Data.Monoid hiding (Sum, Product)
import Data.Typeable

instance NFData Proof where
  rnf (Equated t1 t2) = t1 `seq` t2 `seq` ()

  -- Add more as needed
  rnf _ = ()

instance NFData Unifier where
  rnf m = m `seq` ()

member = [
          -- x is a member of x:xs
          HornClause (predicate "member" ( Var "x" :: Var Int
                                         , List $ VarCons (toTerm (Var "x" :: Var Int))
                                                          (Var "_")
                                         ))
                      Top
          -- x is a member of _:xs if x is a member of xs
         , HornClause (predicate "member" ( Var "x" :: Var Int
                                          , List $ VarCons (toTerm (Var "_" :: Var Int))
                                                           (Var "xs")
                                          ))
                      (PredGoal (predicate "member" (Var "x" :: Var Int, Var "xs" :: Var [Int])) member)
         ]

-- All humans are mortal
mortal = HornClause (predicate "mortal" (Var "x" :: Var String))
                    (PredGoal (predicate "human" (Var "x" :: Var String)) human)
human = [
          -- Hypatia is human
          HornClause (predicate "human" "hypatia") Top
          -- So is Fred
        , HornClause (predicate "human" "fred") Top
        ]

simpleBinary = HornClause (predicate "foo" ('a', 'b')) Top

simpleSubGoal = HornClause (predicate "foo" 'a')
                           (PredGoal (predicate "bar" 'a') [HornClause (predicate "bar" 'a') Top])

uninstantiatedVariablesError = "Variables are not sufficiently instantiated."

test = describeModule "Control.Hspl.Internal.Solver" $ do
  describe "provePredicateWith" $ do
    let runTest p c = observeAllSolver $ provePredicateWith solverCont p c
    it "should prove an axiom" $
      runTest (predicate "foo" ('a', 'b')) simpleBinary `shouldBe`
        [(Resolved (predicate "foo" ('a', 'b')) ProvedTop, mempty)]
    it "should prove a result that follows from a subgoal" $ do
      let (proofs, _) =
            unzip $ runTest (predicate "mortal" "hypatia") mortal
      proofs `shouldBe`
        [Resolved (predicate "mortal" "hypatia")
                  (Resolved (predicate "human" "hypatia") ProvedTop)
        ]
    it "should return unifications made in the goal" $ do
      let (_, us) = unzip $ runTest (predicate "foo" (Var "x" :: Var Char)) simpleSubGoal
      length us `shouldBe` 1
      head us `shouldSatisfy` ('a' // Var "x" `isSubunifierOf`)
  describe "proveUnifiableWith" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> [ProofResult]
        runTest t1 t2 =
          observeAllSolver $ proveUnifiableWith solverCont (toTerm t1) (toTerm t2)
    it "should unify terms when possible" $ do
      let (proofs, us) = unzip $ runTest (Var "x" :: Var String) "foo"
      proofs `shouldBe` [Unified (toTerm "foo") (toTerm "foo")]
      length us `shouldBe` 1
      head us `shouldSatisfy` ("foo" // Var "x" `isSubunifierOf`)
    it "should fail when terms cannot be unified" $
      runTest "bar" "foo" `shouldBe` []
  describe "proveIdenticalWith" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> [ProofResult]
        runTest t1 t2 =
          observeAllSolver $ proveIdenticalWith solverCont (toTerm t1) (toTerm t2)
    it "should fail if the terms are not equal" $
      runTest "foo" "bar" `shouldBe` []
    it "should fail if the terms are not yet unified" $
      runTest (Var "x" :: Var String) "foo" `shouldBe` []
    it "should succeed, but not create new bindings, if the terms are identical" $
      runTest "foo" "foo" `shouldBe`
        [(Identified (toTerm "foo") (toTerm "foo"), mempty)]
  describe "proveEqualWith" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> [ProofResult]
        runTest lhs rhs =
          observeAllSolver $ proveEqualWith solverCont (toTerm lhs) (toTerm rhs)
    it "should unify a variable with a constant" $ do
      let (proofs, us) = unzip $ runTest (Var "x" :: Var Int) (1 :: Int)
      proofs `shouldBe` [Equated (toTerm (1 :: Int)) (toTerm (1 :: Int))]
      length us `shouldBe` 1
      head us `shouldSatisfy` ((1 :: Int) // Var "x" `isSubunifierOf`)
    it "should evaluate an arithmetic expression" $ do
      let (proofs, us) = unzip $ runTest (5 :: Int) (Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))
      proofs `shouldBe` [Equated (toTerm (5 :: Int)) (Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))]
      us `shouldBe` [mempty]
    it "should evaluate arithmetic sub-expressions" $ do
      let lhs = toTerm $ Just (5 :: Int)
      let rhs = adt Just $ Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))
      let (proofs, us) = unzip $ runTest lhs rhs
      proofs `shouldBe` [Equated lhs rhs]
      us `shouldBe` [mempty]
    it "should evaluate and unify sub-expressions" $ do
      let rhs = toTerm $ adt Just $ Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))
      let (proofs, us) = unzip $ runTest (adt Just (Var "x" :: Var Int)) rhs
      proofs `shouldBe` [Equated (toTerm $ Just (5 :: Int)) rhs]
      us `shouldBe` [(5 :: Int) // Var "x"]
    it "should fail when the left-hand side does not unify with the result of the right" $
      runTest (5 :: Int) (Product (toTerm (3 :: Int)) (toTerm (2 :: Int))) `shouldBe` []
    it "should error when the right-hand side contains uninstantiated variables" $
      assertError uninstantiatedVariablesError $
        runTest (Var "x" :: Var Int) (Sum (toTerm (42 :: Int)) (toTerm (Var "y" :: Var Int)))
  describe "proveLessThanWith" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
                   a -> b -> [ProofResult]
        runTest lhs rhs = observeAllSolver $ proveLessThanWith solverCont (toTerm lhs) (toTerm rhs)
    it "should succeed when the left-hand side is less than the right-hand side" $ do
      let (proofs, us) = unzip $ runTest 'a' 'b'
      proofs `shouldBe` [ProvedLessThan 'a' 'b']
      us `shouldBe` [mempty]
    it "should simplify terms before comparing" $ do
      let (proofs, us) = unzip $ runTest (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                         (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
      proofs `shouldBe` [ProvedLessThan (5 :: Int) (6 :: Int)]
      us `shouldBe` [mempty]
    it "should fail when the left-hand side is not less than the right-hand side" $ do
      runTest 'b' 'b' `shouldBe` []
      runTest 'b' 'a' `shouldBe` []
      runTest (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
              (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int))) `shouldBe` []
      runTest (Product (toTerm (2 :: Int)) (toTerm (4 :: Int)))
              (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int))) `shouldBe` []
    it "should error when the left-hand side contains uninstantiated variables" $
      assertError uninstantiatedVariablesError $
        runTest (Var "x" :: Var Char) 'b'
    it "should error when the right-hand side contains uninstantiated variables" $
      assertError uninstantiatedVariablesError $
        runTest 'a' (Var "x" :: Var Char)
  describe "proveNotWith" $ do
    let runTest g = observeAllSolver $ proveNotWith solverCont g
    it "should fail if the inner goal succeeds" $
      runTest (PredGoal (predicate "foo" ('a', 'b')) [simpleBinary]) `shouldBe` []
    it "should succeed if the inner goal fails" $
      runTest (PredGoal (predicate "foo" ('b', 'a')) [simpleBinary]) `shouldBe`
        [(Negated $ PredGoal (predicate "foo" ('b', 'a')) [simpleBinary], mempty)]
  describe "proveAndWith" $ do
    let runTest g1 g2 = observeAllSolver $ proveAndWith solverCont g1 g2
    it "should succeed when both subgoals succeed" $ do
      let (proofs, _) = unzip $ runTest (Identical (toTerm 'a') (toTerm 'a'))
                                        (Identical (toTerm 'b') (toTerm 'b'))
      proofs `shouldBe` [ProvedAnd (Identified (toTerm 'a') (toTerm 'a'))
                                   (Identified (toTerm 'b') (toTerm 'b'))]
    it "should fail when the left subgoal fails" $
      runTest (Identical (toTerm 'a') (toTerm 'b')) (Identical (toTerm 'c') (toTerm 'c')) `shouldBe`
        []
    it "should fail when the right subgoal fails" $
      runTest (Identical (toTerm 'a') (toTerm 'a')) (Identical (toTerm 'b') (toTerm 'c')) `shouldBe`
        []
    it "should return any unifications made in either goal" $ do
      let (_, us) = unzip $ runTest (CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char)))
                                    (CanUnify (toTerm (Var "y" :: Var Bool)) (toTerm True))
      length us `shouldBe` 1
      head us `shouldSatisfy` (('a' // Var "x" <> True // Var "y") `isSubunifierOf`)
    it "should apply unifications made while proving the left-hand side to the right-hand side" $
      runTest (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'a'))
              (CanUnify (toTerm 'b') (toTerm (Var "x" :: Var Char))) `shouldBe` []
  describe "an Or goal" $ do
    let runTest g1 g2 = observeAllSolver $ proveWith solverCont (Or g1 g2)
    it "should succeed when only the left goal succeeds" $ do
      -- Left goal succeeds once, right goal fails
      let (proofs, _) = unzip $ runTest (PredGoal (predicate "mortal" "hypatia") [mortal])
                                        (PredGoal (predicate "fake" ()) [])
      proofs `shouldBe` [ProvedLeft (Resolved (predicate "mortal" "hypatia")
                                              (Resolved (predicate "human" "hypatia") ProvedTop))
                                    (PredGoal (predicate "fake" ()) [])]
      -- Left goals succeeds multiple times, right goal fails
      let (proofs, us) = unzip $ runTest (PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal])
                                         (PredGoal (predicate "fake" ()) [])
      proofs `shouldBePermutationOf` [ ProvedLeft (Resolved (predicate "mortal" "hypatia")
                                                            (Resolved (predicate "human" "hypatia") ProvedTop))
                                                  (PredGoal (predicate "fake" ()) [])
                                     , ProvedLeft (Resolved (predicate "mortal" "fred")
                                                            (Resolved (predicate "human" "fred") ProvedTop))
                                                  (PredGoal (predicate "fake" ()) [])
                                     ]
      length us `shouldBe` 2
      if "hypatia" // Var "x" `isSubunifierOf` head us
        then last us `shouldSatisfy` ("fred" // Var "x" `isSubunifierOf`)
        else do head us `shouldSatisfy` ("fred" // Var "x" `isSubunifierOf`)
                last us `shouldSatisfy` ("hypatia" // Var "x" `isSubunifierOf`)
    it "should succeed when only the right goal succeeds" $ do
      -- Right goal succeeds once, left goal fails
      let (proofs, _) = unzip $ runTest (PredGoal (predicate "fake" ()) [])
                                        (PredGoal (predicate "mortal" "hypatia") [mortal])
      proofs `shouldBe` [ProvedRight (PredGoal (predicate "fake" ()) [])
                                     (Resolved (predicate "mortal" "hypatia")
                                               (Resolved (predicate "human" "hypatia") ProvedTop))]
      -- Right goals succeeds multiple times, left goal fails
      let (proofs, us) = unzip $ runTest (PredGoal (predicate "fake" ()) [])
                                         (PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal])
      proofs `shouldBePermutationOf` [ ProvedRight (PredGoal (predicate "fake" ()) [])
                                                   (Resolved (predicate "mortal" "hypatia")
                                                             (Resolved (predicate "human" "hypatia") ProvedTop))
                                     , ProvedRight (PredGoal (predicate "fake" ()) [])
                                                   (Resolved (predicate "mortal" "fred")
                                                             (Resolved (predicate "human" "fred") ProvedTop))
                                     ]
      length us `shouldBe` 2
      if "hypatia" // Var "x" `isSubunifierOf` head us
        then last us `shouldSatisfy` ("fred" // Var "x" `isSubunifierOf`)
        else do head us `shouldSatisfy` ("fred" // Var "x" `isSubunifierOf`)
                last us `shouldSatisfy` ("hypatia" // Var "x" `isSubunifierOf`)
    it "should succeed once for each subgoal that succeeds" $ do
      let (proofs, _) = unzip $ runTest (PredGoal (predicate "mortal" "hypatia") [mortal])
                                        (PredGoal (predicate "mortal" "fred") [mortal])
      proofs `shouldBe` [ ProvedLeft (Resolved (predicate "mortal" "hypatia")
                                               (Resolved (predicate "human" "hypatia") ProvedTop))
                                     (PredGoal (predicate "mortal" "fred") [mortal])
                        , ProvedRight (PredGoal (predicate "mortal" "hypatia") [mortal])
                                      (Resolved (predicate "mortal" "fred")
                                                (Resolved (predicate "human" "fred") ProvedTop))
                        ]
    it "should fail when both goals fail" $
      runTest (PredGoal (predicate "fake" ()) []) (PredGoal (predicate "fake" ()) []) `shouldBe` []
  describe "proveTopWith" $
    it "should always succeed" $
      observeAllSolver (proveTopWith solverCont) `shouldBe` [(ProvedTop, mempty)]
  describe "proveBottomWith" $
    it "should always fail" $
      observeAllSolver (proveBottomWith solverCont) `shouldBe` []
  describe "an Alternatives proof" $ do
    let runTest x g xs = observeAllSolver $ proveAlternativesWith solverCont x g xs
    let xIsAOrB = Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                     (CanUnify (toTerm $ Var "x") (toTerm 'b'))
    let x :: Term Char
        x = toTerm $ Var "x"
        xs :: Term [Char]
        xs = toTerm $ Var "xs"
    it "should unify a variable with a list of alternatives" $ do
      let (ps, us) = unzip $ runTest x xIsAOrB xs
      ps `shouldBe` [FoundAlternatives x xIsAOrB (toTerm ['a', 'b'])
                                       [ ProvedLeft (Unified (toTerm 'a') (toTerm 'a'))
                                                    (CanUnify x (toTerm 'b'))
                                       , ProvedRight (CanUnify x (toTerm 'a'))
                                                     (Unified (toTerm 'b') (toTerm 'b'))
                                       ]]
      length us `shouldBe` 1
      head us `shouldSatisfy` (['a', 'b'] // Var "xs" `isSubunifierOf`)
    it "should succeed even if the inner goal fails" $ do
      let (ps, us) = unzip $ runTest x Bottom xs
      ps `shouldBe` [FoundAlternatives x Bottom (List Nil) []]
      length us `shouldBe` 1
      head us `shouldSatisfy` (List Nil // (Var "xs" :: Var [Char]) `isSubunifierOf`)
    it "should fail if the output term does not unify with the alternatives" $ do
      runTest x xIsAOrB (toTerm [Var "y" :: Var Char]) `shouldBe` []
      runTest x Bottom (List $ VarCons (toTerm (Var "y" :: Var Char)) (Var "ys")) `shouldBe` []
    it "should handle complex templates" $ do
      let (ps, us) = unzip $ runTest (adt Just x) xIsAOrB (toTerm (Var "xs" :: Var [Maybe Char]))
      ps `shouldBe` [FoundAlternatives (adt Just x) xIsAOrB (toTerm [Just 'a', Just 'b'])
                                       [ ProvedLeft (Unified (toTerm 'a') (toTerm 'a'))
                                                    (CanUnify x (toTerm 'b'))
                                       , ProvedRight (CanUnify x (toTerm 'a'))
                                                     (Unified (toTerm 'b') (toTerm 'b'))
                                       ]]
      length us `shouldBe` 1
      head us `shouldSatisfy` ([Just 'a', Just 'b'] // Var "xs" `isSubunifierOf`)
    it "should take place in the same environment as the parent goal" $ do
      let g = PredGoal (predicate "foo" 'a')
                       [HornClause (predicate "foo" (Var "x" :: Var Char))
                                   (Alternatives (toTerm (Var "y" :: Var Char))
                                                 (Equal (toTerm (Var "y" :: Var Char)) (toTerm $ Var "x"))
                                                 (toTerm [Var "x"]))
                       ]
      let (ps, _) = unzip $ runHspl g
      length ps `shouldBe` 1
      case head ps of
        Resolved p proof -> do
          p `shouldBe` predicate "foo" 'a'
          case proof of
            FoundAlternatives x g xs proofs -> do
              case cast x of
                Just (x' :: Term Char) -> x' `shouldBeAlphaEquivalentTo` (Var "y" :: Var Char)
                Nothing -> failure $ "Expected y :: Char, but got " ++ show x
              case cast xs of
                Just xs' -> xs' `shouldBe` toTerm ['a']
                Nothing -> failure $ "Expected ['a'], but got " ++ show xs
              proofs `shouldBe` [Equated (toTerm 'a') (toTerm 'a')]
              case g of
                Equal t1 t2 -> do
                  case cast t1 of
                    Just (t1' :: Term Char) -> t1' `shouldBeAlphaEquivalentTo` (Var "y" :: Var Char)
                    Nothing -> failure $ "Expected y :: Char, but got " ++ show t1
                  case cast t2 of
                    Just t2' -> t2' `shouldBe` toTerm 'a'
                    Nothing -> failure $ "Expected 'a', but got " ++ show t2
                _ -> failure $ "Expected Equal y 'a', but got " ++ show g
            _ -> failure $ "Expected FoundAlternatives y (Equal y 'a') ['a'], but got " ++ show proof
        _ -> failure $ "Expected Resolved foo('a') (FoundAlternatives y (Equal y 'a') ['a']), " ++
                       "but got " ++ show (head ps)
    when "the template variable is already bound" $
      it "should return a list of the bound variable" $ do
        let (ps, us) = unzip $ runHspl $  CanUnify (toTerm $ Var "y") (toTerm 'c')
                                       <> Alternatives (toTerm $ Var "y") xIsAOrB xs
        ps `shouldBe` [ProvedAnd (Unified (toTerm 'c') (toTerm 'c'))
                                 (FoundAlternatives (toTerm 'c') xIsAOrB (toTerm ['c', 'c'])
                                    [ ProvedLeft (Unified (toTerm 'a') (toTerm 'a'))
                                                 (CanUnify x (toTerm 'b'))
                                    , ProvedRight (CanUnify x (toTerm 'a'))
                                                  (Unified (toTerm 'b') (toTerm 'b'))
                                    ])]
        length us `shouldBe` 1
        head us `shouldSatisfy` (['c', 'c'] // Var "xs" `isSubunifierOf`)
    when "the template variable is unbound" $
      it "should return a list of variables" $ do
        let (ps, us) = unzip $ runTest x Top xs
        ps `shouldBe` [FoundAlternatives x Top (toTerm [x]) [ProvedTop]]
        length us `shouldBe` 1
        head us `shouldSatisfy` ([x] // Var "xs" `isSubunifierOf`)
  describe "proveOnceWith" $ do
    let runTest g = observeAllSolver $ proveOnceWith solverCont g
    it "should fail if the inner goal fails" $
      runTest Bottom `shouldBe` []
    it "should succeed if the inner goal succeeds" $ do
      let (ps, us) = unzip $ runTest (PredGoal (predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char)) [simpleBinary])
      ps `shouldBe` [ProvedOnce $ Resolved (predicate "foo" ('a', 'b')) ProvedTop]
      length us `shouldBe` 1
      head us `shouldSatisfy` (('a' // Var "x" <> 'b' // Var "y") `isSubunifierOf`)

      let (ps, us) = unzip $ runTest (PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal])
      ps `shouldBe` [ProvedOnce $ Resolved (predicate "mortal" "hypatia")
                                           (Resolved (predicate "human" "hypatia") ProvedTop)]
      length us `shouldBe` 1
      head us `shouldSatisfy` ("hypatia" // Var "x" `isSubunifierOf`)
  describe "a proof search" $ do
    let search p = searchProof (p, mempty)
    it "should traverse every branch of the proof" $ do
      let p = predicate "p" ()
      let q = predicate "q" ()
      let r = predicate "r" ()
      let deepProof = Resolved p (Resolved q (Resolved r ProvedTop))
      search (Resolved p ProvedTop) (PredGoal p []) `shouldBe` [PredGoal p []]
      search deepProof (PredGoal p []) `shouldBe` [PredGoal p []]
      search deepProof (PredGoal q []) `shouldBe` [PredGoal q []]
      search deepProof (PredGoal r []) `shouldBe` [PredGoal r []]
    it "should find subgoals which unify with the query" $
      search (Resolved (predicate "p" (Var "x" :: Var Char, 'b'))
                       (Resolved (predicate "p" ('a', Var "x" :: Var Char)) ProvedTop))
             (PredGoal (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char)) [])
        `shouldBePermutationOf`
        [ PredGoal (predicate "p" (Var "x" :: Var Char, 'b')) []
        , PredGoal (predicate "p" ('a', Var "x" :: Var Char)) []
        ]
    context "of a ProvedAnd proof" $ do
      it "should unify a goal with a proven conjunction" $ do
        let leftProof = Identified (toTerm 'a') (toTerm 'a')
        let rightProof = Identified (toTerm 'b') (toTerm 'b')
        let leftGoal = getSolution (leftProof, mempty)
        let rightGoal = getSolution (rightProof, mempty)
        search (ProvedAnd leftProof rightProof) (And leftGoal rightGoal) `shouldBe` [And leftGoal rightGoal]
      it "should recursively search the proof of a conjunction" $ do
        let leftProof = Identified (toTerm 'a') (toTerm 'a')
        let rightProof = Identified (toTerm 'b') (toTerm 'b')
        let leftGoal = getSolution (leftProof, mempty)
        let rightGoal = getSolution (rightProof, mempty)
        search (ProvedAnd leftProof rightProof) leftGoal `shouldBe` [leftGoal]
        search (ProvedAnd leftProof rightProof) rightGoal `shouldBe` [rightGoal]
    context "of a ProvedOr proof" $ do
      it "should unify a goal with a proven disjunction" $ do
        let unprovenGoal = Identical (toTerm 'a') (toTerm 'b')
        let provenGoal = Equal (toTerm 'a') (toTerm 'a')
        let subProof = Equated (toTerm 'a') (toTerm 'a')
        search (ProvedLeft subProof unprovenGoal) (Or provenGoal unprovenGoal) `shouldBe`
          [Or provenGoal unprovenGoal]
        search (ProvedRight unprovenGoal subProof) (Or unprovenGoal provenGoal) `shouldBe`
          [Or unprovenGoal provenGoal]
      it "should recursively search the proof of a disjunction" $ do
        let unprovenGoal = Identical (toTerm 'a') (toTerm 'b')
        let p = predicate "p" 'a'
        let subProof = Resolved p ProvedTop
        let provenGoal = getSolution (subProof, mempty)
        search (ProvedLeft subProof unprovenGoal) provenGoal `shouldBe` [provenGoal]
        search (ProvedRight unprovenGoal subProof) provenGoal `shouldBe` [provenGoal]
      it "should not unify a goal with the unproven goal in a proof of a disjunction" $ do
        let unprovenGoal = Identical (toTerm 'a') (toTerm 'b')
        let subProof = Equated (toTerm 'a') (toTerm 'a')
        search (ProvedLeft subProof unprovenGoal) unprovenGoal `shouldBe` []
        search (ProvedRight unprovenGoal subProof) unprovenGoal `shouldBe` []
    context "of a FoundAlternatives proof" $ do
      it "should unify a goal with the proven Alternatives goal" $
        search (FoundAlternatives (toTerm (Var "x" :: Var Char))
                                  (Equal (toTerm $ Var "x") (toTerm 'a'))
                                  (toTerm ['a'])
                                  [Equated (toTerm 'a') (toTerm 'a')])
               (Alternatives (toTerm (Var "a" :: Var Char))
                             (Equal (toTerm (Var "b" :: Var Char)) (toTerm $ Var "c"))
                             (toTerm (Var "d"))) `shouldBe`
          [Alternatives (toTerm (Var "x" :: Var Char))
                        (Equal (toTerm $ Var "x") (toTerm 'a'))
                        (toTerm ['a'])]
      it "should recursively search each subproof" $
        search (FoundAlternatives (toTerm (Var "x" :: Var Char))
                                  (Equal (toTerm $ Var "x") (toTerm 'a'))
                                  (toTerm ['a'])
                                  [ Equated (toTerm 'a') (toTerm 'a')
                                  , Equated (toTerm 'a') (toTerm 'b') -- ???
                                  ])
               (Equal (toTerm (Var "x" :: Var Char)) (toTerm $ Var "y")) `shouldBe`
          [Equal (toTerm 'a') (toTerm 'a'), Equal (toTerm 'a') (toTerm 'b')]
    context "of binary term proofs" $ do
      let constrs :: [(Term Char -> Term Char -> Proof, Term Char -> Term Char -> Goal)]
          constrs = [ (Identified, Identical)
                    , (Unified, CanUnify)
                    , (Equated, Equal)
                    ]
      withParams constrs $ \(proof, term) ->
        it "should unify a query goal" $
          search (proof (toTerm 'a') (toTerm 'a'))
                 (term (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
            [term (toTerm 'a') (toTerm 'a')]
      it "should unify a query goal" $
        search (ProvedLessThan 'a' 'a')
               (LessThan (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
            [LessThan (toTerm 'a') (toTerm 'a')]
    context "of a Negated proof" $
      it "should unify a query goal" $
        search (Negated $ Identical (toTerm 'a') (toTerm 'b'))
               (Not $ Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          [Not (Identical (toTerm 'a') (toTerm 'b'))]
    context "of unitary logic proofs" $
      it "should unify a query goal" $
        search ProvedTop Top `shouldBe` [Top]
    context "of a ProvedOnce proof" $ do
      it "should unify a query goal" $
        search (ProvedOnce ProvedTop) (Once Top) `shouldBe` [Once Top]
      it "should recursively search the subproof" $
        search (ProvedOnce ProvedTop) Top `shouldBe` [Top]
  describe "the \"get solutions\" feature" $ do
    it "should return the theorem at the root of a proof tree" $ do
      let get p = getSolution (p, mempty)
      get (Resolved (predicate "p" ()) (Resolved (predicate "s" ()) ProvedTop)) `shouldBe`
        PredGoal (predicate "p" ()) []
      get (Unified (toTerm 'a') (toTerm 'a')) `shouldBe` CanUnify (toTerm 'a') (toTerm 'a')
      get (Identified (toTerm 'a') (toTerm 'a')) `shouldBe` Identical (toTerm 'a') (toTerm 'a')
      get (Equated (toTerm (1 :: Int)) (toTerm (1 :: Int))) `shouldBe`
        Equal (toTerm (1 :: Int)) (toTerm (1 :: Int))
      get (ProvedLessThan 'a' 'b') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
      get (ProvedAnd (Equated (toTerm 'a') (toTerm 'a'))
                     (Identified (toTerm 'b') (toTerm 'b'))) `shouldBe`
        And (Equal (toTerm 'a') (toTerm 'a')) (Identical (toTerm 'b') (toTerm 'b'))
      get (ProvedLeft (Equated (toTerm 'a') (toTerm 'a'))
                      (Identical (toTerm 'a') (toTerm 'b'))) `shouldBe`
        Or (Equal (toTerm 'a') (toTerm 'a')) (Identical (toTerm 'a') (toTerm 'b'))
      get (ProvedRight (Identical (toTerm 'a') (toTerm 'b'))
                      (Equated (toTerm 'a') (toTerm 'a'))) `shouldBe`
        Or (Identical (toTerm 'a') (toTerm 'b')) (Equal (toTerm 'a') (toTerm 'a'))
      get ProvedTop `shouldBe` Top
      get (FoundAlternatives (toTerm (Var "x" :: Var Char))
                                     (Equal (toTerm $ Var "x") (toTerm 'a'))
                                     (toTerm ['a'])
                                     [Equated (toTerm 'a') (toTerm 'a')]) `shouldBe`
        Alternatives (toTerm (Var "x" :: Var Char))
                     (Equal (toTerm $ Var "x") (toTerm 'a'))
                     (toTerm ['a'])
    it "should get all solutions from a forest of proof tress" $
      getAllSolutions [ (Resolved (predicate "p" ()) ProvedTop, mempty)
                      , (Resolved (predicate "q" ()) ProvedTop, mempty)] `shouldBe`
        [PredGoal (predicate "p" ()) [], PredGoal (predicate "q" ()) []]
  describe "the \"get unifiers\" feature" $ do
    it "should return the unifier from a solution" $ do
      let u = toTerm 'a' // Var "x" <> toTerm True // Var "y"
      getUnifier (Resolved (predicate "foo" ()) ProvedTop, u) `shouldBe` u
    it "should return all unifiers from a solution forest" $ do
      let u1 = toTerm 'a' // Var "x"
      let u2 = toTerm True // Var "y"
      getAllUnifiers [ (Resolved (predicate "foo" ()) ProvedTop, u1)
                     , (Resolved (predicate "bar" ()) ProvedTop, u2)
                     ] `shouldBe`
        [u1, u2]
  describe "the HSPL solver" $ do
    it "should return all proofs of the query" $ do
      let (proofs, _) = unzip $ runHspl $ PredGoal (predicate "mortal" "hypatia") [mortal]
      proofs `shouldBe` [Resolved (predicate "mortal" "hypatia")
                                  (Resolved (predicate "human" "hypatia") ProvedTop)
                        ]
      let (proofs2, _) = unzip $ runHspl $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      proofs2 `shouldBePermutationOf`
        [ Resolved (predicate "mortal" "hypatia")
                   (Resolved (predicate "human" "hypatia") ProvedTop)
        , Resolved (predicate "mortal" "fred")
                   (Resolved (predicate "human" "fred") ProvedTop)
        ]
    it "should return the requested number of proofs" $ do
      let (proofs, _) = unzip $ runHsplN 1 $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      proofs `shouldBeSubsetOf`
        [ Resolved (predicate "mortal" "hypatia")
                   (Resolved (predicate "human" "hypatia") ProvedTop)
        , Resolved (predicate "mortal" "fred")
                   (Resolved (predicate "human" "fred") ProvedTop)
        ]
      length proofs `shouldBe` 1
    it "should indicate when variables have been substituted" $ do
      let (_, us) = unzip $ runHspl $ PredGoal (predicate "member" (Var "x" :: Var Int, [1 :: Int])) member
      length us `shouldBe` 1
      head us `shouldSatisfy` (((1 :: Int) // Var "x") `isSubunifierOf`)
    it "should return a unifier for each solution" $ do
      let (_, us) = unzip $ runHspl $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      length us `shouldBe` 2
      if ("hypatia" // Var "x") `isSubunifierOf` head us
        then last us `shouldSatisfy` (("fred" // Var "x") `isSubunifierOf`)
        else do head us `shouldSatisfy` (("fred" // Var "x") `isSubunifierOf`)
                last us `shouldSatisfy` (("hypatia" // Var "x") `isSubunifierOf`)
