{-# LANGUAGE TypeFamilies #-} -- For equational constraints

module SolverTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.Unification hiding (Unified)
import Data.Monoid hiding (Sum, Product)

member = [
          -- x is a member of x:xs
          HornClause (predicate "member" ( Var "x" :: Var Int
                                          , List (toTerm (Var "x" :: Var Int))
                                                 (toTerm (Var "_" :: Var [Int]))))
                      []
          -- x is a member of _:xs if x is a member of xs
         , HornClause (predicate "member" ( Var "x" :: Var Int
                                          , List (toTerm (Var "_" :: Var Int))
                                                 (toTerm (Var "xs" :: Var [Int]))))
                      [PredGoal (predicate "member" (Var "x" :: Var Int, Var "xs" :: Var [Int])) member]
         ]

-- All humans are mortal
mortal = HornClause (predicate "mortal" (Var "x" :: Var String))
                    [PredGoal (predicate "human" (Var "x" :: Var String)) human]
human = [
          -- Hypatia is human
          HornClause (predicate "human" "hypatia") []
          -- So is Fred
        , HornClause (predicate "human" "fred") []
        ]

simpleBinary = HornClause (predicate "foo" ('a', 'b')) []

subGoals = HornClause ( predicate "subGoals" (Var "x" :: Var Char, Var "y" :: Var Char))
                      [ PredGoal (predicate "subGoal1" (Var "x" :: Var Char)) subGoal1
                      , PredGoal (predicate "subGoal2" (Var "y" :: Var Char)) subGoal2
                      ]
subGoal1 = [HornClause (predicate "subGoal1" 'a') []]
subGoal2 = [HornClause (predicate "subGoal2" 'b') []]

simpleSubGoal = HornClause (predicate "foo" 'a')
                           [PredGoal (predicate "bar" 'a')
                                     [HornClause (predicate "bar" 'a') []]
                           ]

-- This program illustrates a potential bug in a naive impementation. There should be no solutions
-- to foo(X). The unifier ['a'/X] which results from proving bar(X) should be applied to the next
-- subgoal, giving baz('a'), which clearly has no solutions. A naive implementation fails to apply
-- the intermediate unifier to the second subgoal, giving the erronious solution foo('b').
unifierTrap = HornClause ( predicate "foo" (Var "x" :: Var Char))
                         [ PredGoal (predicate "bar" (Var "x" :: Var Char))
                                    [HornClause (predicate "bar" 'a') []]
                         , PredGoal (predicate "baz" (Var "x" :: Var Char))
                                    [HornClause (predicate "baz" 'b') []]
                         ]

test = describeModule "Control.Hspl.Internal.Solver" $ do
  describe "provePredicateWith" $ do
    let runTest p c = observeAllSolver $ provePredicateWith solverCont p c
    it "should prove an axiom" $
      runTest (predicate "foo" ('a', 'b')) simpleBinary `shouldBe`
        [(Resolved (predicate "foo" ('a', 'b')) [], mempty)]
    it "should prove a result that follows from subgoals" $ do
      let (proofs, us) =
            unzip $ runTest (predicate "subGoals" (Var "x" :: Var Char, Var "y" :: Var Char)) subGoals
      proofs `shouldBe`
        [Resolved ( predicate "subGoals" ('a', 'b'))
                  [ Resolved (predicate "subGoal1" 'a') []
                  , Resolved (predicate "subGoal2" 'b') []
                  ]
        ]
      length us `shouldBe` 1
      head us `shouldSatisfy` (('a' // Var "x" <> 'b' // Var "y") `isSubunifierOf`)
    it "should successively apply the unifier to subgoals" $
      runTest (predicate "foo" (Var "x" :: Var Char)) unifierTrap `shouldBe` []
    it "should unify the goal with the clause" $ do
      let (proofs, _) = unzip $ runTest (predicate "subGoals" ('a', 'b')) subGoals
      proofs `shouldBe`
        [Resolved ( predicate "subGoals" ('a', 'b'))
                  [ Resolved (predicate "subGoal1" 'a') []
                  , Resolved (predicate "subGoal2" 'b') []
                  ]
        ]
      runTest (predicate "subGoals" 'b') subGoals `shouldBe` []
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
  describe "proveNotWith" $ do
    let runTest g = observeAllSolver $ proveNotWith solverCont g
    it "should fail if the inner goal succeeds" $
      runTest (PredGoal (predicate "foo" ('a', 'b')) [simpleBinary]) `shouldBe` []
    it "should succeed if the inner goal fails" $
      runTest (PredGoal (predicate "foo" ('b', 'a')) [simpleBinary]) `shouldBe`
        [(Negated $ PredGoal (predicate "foo" ('b', 'a')) [simpleBinary], mempty)]
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
    it "should fail when the left-hand side does not unify with the result of the right" $
      runTest (5 :: Int) (Product (toTerm (3 :: Int)) (toTerm (2 :: Int))) `shouldBe` []
  describe "a proof search" $ do
    it "should traverse every branch of the proof" $ do
      let p = predicate "p" ()
      let q = predicate "q" ()
      let r = predicate "r" ()
      let wideProof = (Resolved p [Resolved p [], Resolved q [], Resolved r []], mempty)
      let deepProof = (Resolved p [Resolved q [Resolved r []]], mempty)
      searchProof (Resolved p [], mempty) (PredGoal p []) `shouldBe` [PredGoal p []]
      searchProof wideProof (PredGoal p []) `shouldBe` [PredGoal p [], PredGoal p []]
      searchProof wideProof (PredGoal q []) `shouldBe` [PredGoal q []]
      searchProof wideProof (PredGoal r []) `shouldBe` [PredGoal r []]
      searchProof deepProof (PredGoal p []) `shouldBe` [PredGoal p []]
      searchProof deepProof (PredGoal q []) `shouldBe` [PredGoal q []]
      searchProof deepProof (PredGoal r []) `shouldBe` [PredGoal r []]
    it "should find subgoals which unify with the query" $
      searchProof (Resolved (predicate "p" (Var "x" :: Var Char, 'b'))
                            [Resolved (predicate "p" ('a', Var "x" :: Var Char)) []], mempty)
                  (PredGoal (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char)) [])
        `shouldBePermutationOf`
        [ PredGoal (predicate "p" (Var "x" :: Var Char, 'b')) []
        , PredGoal (predicate "p" ('a', Var "x" :: Var Char)) []
        ]
    it "should work for all types of goals" $ do
      searchProof (Identified (toTerm 'a') (toTerm 'a'), mempty)
                  (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
        [Identical (toTerm 'a') (toTerm 'a')]
      searchProof (Unified (toTerm 'a') (toTerm 'a'), mempty)
                  (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
        [CanUnify (toTerm 'a') (toTerm 'a')]
      searchProof (Equated (toTerm (3 :: Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int))), mempty)
                  (Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))) `shouldBe`
        [Equal (toTerm (3 :: Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))]
      searchProof (Negated $ Identical (toTerm 'a') (toTerm 'b'), mempty)
                  (Not $ Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)))
        `shouldBe`
        [Not (Identical (toTerm 'a') (toTerm 'b'))]
  describe "the \"get solutions\" feature" $ do
    it "should return the theorem at the root of a proof tree" $ do
      getSolution (Resolved (predicate "p" ())
                            [ Resolved (predicate "q" ())
                                       [Resolved (predicate "r" ()) []]
                            , Resolved (predicate "s" ()) []
                            ], mempty) `shouldBe`
        PredGoal (predicate "p" ()) []
      getSolution (Unified (toTerm 'a') (toTerm 'a'), mempty) `shouldBe`
        CanUnify (toTerm 'a') (toTerm 'a')
      getSolution (Identified (toTerm 'a') (toTerm 'a'), mempty) `shouldBe`
        Identical (toTerm 'a') (toTerm 'a')
      getSolution (Equated (toTerm (1 :: Int)) (toTerm (1 :: Int)), mempty) `shouldBe`
        Equal (toTerm (1 :: Int)) (toTerm (1 :: Int))
    it "should get all solutions from a forest of proof tress" $
      getAllSolutions [ (Resolved (predicate "p" ()) [], mempty)
                      , (Resolved (predicate "q" ()) [], mempty)] `shouldBe`
        [PredGoal (predicate "p" ()) [], PredGoal (predicate "q" ()) []]
  describe "the \"get unifiers\" feature" $ do
    it "should return the unifier from a solution" $ do
      let u = toTerm 'a' // Var "x" <> toTerm True // Var "y"
      getUnifier (Resolved (predicate "foo" ()) [], u) `shouldBe` u
    it "should return all unifiers from a solution forest" $ do
      let u1 = toTerm 'a' // Var "x"
      let u2 = toTerm True // Var "y"
      getAllUnifiers [ (Resolved (predicate "foo" ()) [], u1)
                     , (Resolved (predicate "bar" ()) [], u2)
                     ] `shouldBe`
        [u1, u2]
  describe "the HSPL solver" $ do
    it "should return all proofs of the query" $ do
      let (proofs, _) = unzip $ runHspl $ PredGoal (predicate "mortal" "hypatia") [mortal]
      proofs `shouldBe` [Resolved (predicate "mortal" "hypatia")
                                  [Resolved (predicate "human" "hypatia") []]
                        ]
      let (proofs2, _) = unzip $ runHspl $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      proofs2 `shouldBePermutationOf`
        [ Resolved (predicate "mortal" "hypatia")
                   [Resolved (predicate "human" "hypatia") []]
        , Resolved (predicate "mortal" "fred")
                   [Resolved (predicate "human" "fred") []]
        ]
    it "should return the requested number of proofs" $ do
      let (proofs, _) = unzip $ runHsplN 1 $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      proofs `shouldBeSubsetOf`
        [ Resolved (predicate "mortal" "hypatia")
                   [Resolved (predicate "human" "hypatia") []]
        , Resolved (predicate "mortal" "fred")
                   [Resolved (predicate "human" "fred") []]
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
