{-# LANGUAGE TypeFamilies #-} -- For equational constraints

module SolverTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.Unification
import Data.Monoid hiding (Sum, Product)

-- x is a member of x:xs
member1 = HornClause (predicate "member" ( Var "x" :: Var Int
                                         , List (toTerm (Var "x" :: Var Int))
                                                (toTerm (Var "_" :: Var [Int]))))
                     []
-- x is a member of _:xs if x is a member of xs
member2 = HornClause (predicate "member" ( Var "x" :: Var Int
                                         , List (toTerm (Var "_" :: Var Int))
                                                (toTerm (Var "xs" :: Var [Int]))))
                     [PredGoal $ predicate "member" (Var "x" :: Var Int, Var "xs" :: Var [Int])]
memberProgram = addClauses [member1, member2] emptyProgram

-- All humans are mortal
mortal = HornClause (predicate "mortal" (Var "x" :: Var String))
                    [PredGoal $ predicate "human" (Var "x" :: Var String)]
-- Hypatia is human
human1 = HornClause (predicate "human" "hypatia") []
-- So is Fred
human2 = HornClause (predicate "human" "fred") []

syllogism = addClauses [mortal, human1, human2] emptyProgram

example0 = addClause (HornClause (predicate "foo" ('a', 'b')) []) emptyProgram

example1 = addClauses [ HornClause ( predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
                                   [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                                   , PredGoal $ predicate "baz" (Var "y" :: Var Char)
                                   ]
                      , HornClause ( predicate "bar" 'a' ) []
                      , HornClause ( predicate "baz" 'b' ) []
                      ] emptyProgram

noUnification = addClauses [HornClause (predicate "foo" (Var "x" :: Var Char)) []] emptyProgram

partialUnification = addClauses [HornClause (predicate "foo" (Var "x" :: Var Char, 'b')) []] emptyProgram

canUnify = addClauses [ HornClause ( predicate "isFoo" (Var "x" :: Var String))
                                   [ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")]
                      ] emptyProgram

identical = addClauses [ HornClause ( predicate "isFoo" (Var "x" :: Var String))
                                    [ Identical (toTerm (Var "x" :: Var String)) (toTerm "foo")]
                       ] emptyProgram

-- This program illustrates a potential bug in a naive impementation. There should be no solutions
-- to foo(X). The unifier ['a'/X] which results from proving bar(X) should be applied to the next
-- subgoal, giving baz('a'), which clearly has no solutions. A naive implementation fails to apply
-- the intermediate unifier to the second subgoal, giving the erronious solution foo('b').
unifierTrap = addClauses [ HornClause ( predicate "foo" (Var "x" :: Var Char))
                                      [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                                      , PredGoal $ predicate "baz" (Var "x" :: Var Char)
                                      ]
                         , HornClause ( predicate "bar" 'a') []
                         , HornClause ( predicate "baz" 'b') []
                         ] emptyProgram

test = describeModule "Control.Hspl.Internal.Solver" $ do
  describe "provePredicateWith" $ do
    let runTest prog p c = observeAllSolver $ provePredicateWith (solverCont prog) prog p c
    it "should prove an axiom" $
      runTest example0
        (predicate "foo" ('a', 'b'))
        (HornClause (predicate "foo" ('a', 'b')) []) `shouldBe`
        [(Axiom $ PredGoal $ predicate "foo" ('a', 'b'), mempty)]
    it "should prove a result that follows from subgoals" $ do
      let (proofs, us) = unzip $ runTest example1
            (predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
            (HornClause ( predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
                        [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                        , PredGoal $ predicate "baz" (Var "y" :: Var Char)
                        ])
      proofs `shouldBe`
        [Proof ( PredGoal $ predicate "foo" ('a', 'b'))
               [ Axiom $ PredGoal $ predicate "bar" 'a'
               , Axiom $ PredGoal $ predicate "baz" 'b']]
      length us `shouldBe` 1
      head us `shouldSatisfy` (('a' // Var "x" <> 'b' // Var "y") `isSubunifierOf`)
    it "should successively apply the unifier to subgoals" $
      runTest unifierTrap
        (predicate "foo" (Var "x" :: Var Char))
        (HornClause ( predicate "foo" (Var "x" :: Var Char))
                    [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                    , PredGoal $ predicate "baz" (Var "x" :: Var Char)
                    ]) `shouldBe` []
    it "should unify the goal with the clause" $ do
      let (proofs, _) = unzip $ runTest example1
            (predicate "foo" ('a', 'b'))
            (HornClause ( predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
                        [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                        , PredGoal $ predicate "baz" (Var "y" :: Var Char)
                        ])
      proofs `shouldBe`
        [Proof ( PredGoal $ predicate "foo" ('a', 'b'))
               [ Axiom $ PredGoal $ predicate "bar" 'a'
               , Axiom $ PredGoal $ predicate "baz" 'b']]
      runTest example1 (predicate "bar" 'b') (HornClause (predicate "bar" 'a') []) `shouldBe` []
  describe "proveUnifiableWith" $ do
    let runTest prog t1 t2 = observeAllSolver $
          proveUnifiableWith (solverCont prog) prog (toTerm t1) (toTerm t2)
    it "should unify terms when possible" $ do
      let (proofs, us) = unzip $ runTest canUnify (Var "x" :: Var String) "foo"
      proofs `shouldBe` [Axiom $ CanUnify (toTerm "foo") (toTerm "foo")]
      length us `shouldBe` 1
      head us `shouldSatisfy` ("foo" // Var "x" `isSubunifierOf`)
    it "should fail when terms cannot be unified" $
      runTest canUnify "bar" "foo" `shouldBe` []
  describe "proveIdenticalWith" $ do
    let runTest prog t1 t2 = observeAllSolver $
          proveIdenticalWith (solverCont prog) prog (toTerm t1) (toTerm t2)
    it "should fail if the terms are not equal" $
      runTest identical "foo" "bar" `shouldBe` []
    it "should fail if the terms are not yet unified" $
      runTest identical (Var "x" :: Var String) "foo" `shouldBe` []
    it "should succeed, but not create new bindings, if the terms are identical" $
      runTest identical "foo" "foo" `shouldBe`
        [(Axiom $ Identical (toTerm "foo") (toTerm "foo"), mempty)]
  describe "proveNotWith" $ do
    let runTest prog g = observeAllSolver $ proveNotWith (solverCont prog) prog g
    it "should fail if the inner goal succeeds" $
      runTest example0 (PredGoal $ predicate "foo" ('a', 'b')) `shouldBe` []
    it "should succeed if the inner goal fails" $
      runTest example0 (PredGoal $ predicate "foo" ('b', 'a')) `shouldBe`
        [(Axiom $ Not $ PredGoal $ predicate "foo" ('b', 'a'), mempty)]
  describe "proveEqualWith" $ do
    let runTest lhs rhs = observeAllSolver $
          proveEqualWith (solverCont emptyProgram) emptyProgram (toTerm lhs) (toTerm rhs)
    it "should unify a variable with a constant" $ do
      let (proofs, us) = unzip $ runTest (Var "x" :: Var Int) (1 :: Int)
      proofs `shouldBe` [Axiom $ Equal (toTerm (1 :: Int)) (toTerm (1 :: Int))]
      length us `shouldBe` 1
      head us `shouldSatisfy` ((1 :: Int) // Var "x" `isSubunifierOf`)
    it "should evaluate an arithmetic expression" $ do
      let (proofs, us) = unzip $ runTest (5 :: Int) (Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))
      proofs `shouldBe` [Axiom $ Equal (toTerm (5 :: Int)) (Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))]
      us `shouldBe` [mempty]
    it "should fail when the left-hand side does not unify with the result of the right" $
      runTest (5 :: Int) (Product (toTerm (3 :: Int)) (toTerm (2 :: Int))) `shouldBe` []
  describe "a proof search" $ do
    it "should traverse every branch of the proof" $ do
      let p = predicate "p" ()
      let q = predicate "q" ()
      let r = predicate "r" ()
      let wideProof = (Proof (PredGoal p) [Axiom $ PredGoal p, Axiom $ PredGoal q, Axiom $ PredGoal r], mempty)
      let deepProof = (Proof (PredGoal p) [Proof (PredGoal q) [Axiom $ PredGoal r]], mempty)
      searchProof (Axiom $ PredGoal p, mempty) p `shouldBe` [p]
      searchProof wideProof p `shouldBe` [p, p]
      searchProof wideProof q `shouldBe` [q]
      searchProof wideProof r `shouldBe` [r]
      searchProof deepProof p `shouldBe` [p]
      searchProof deepProof q `shouldBe` [q]
      searchProof deepProof r `shouldBe` [r]
    it "should find subgoals which unify with the query" $
      searchProof (Proof (PredGoal $ predicate "p" (Var "x" :: Var Char, 'b'))
                         [Axiom . PredGoal $ predicate "p" ('a', Var "x" :: Var Char)], mempty)
                  (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char)) `shouldBePermutationOf`
        [predicate "p" (Var "x" :: Var Char, 'b'), predicate "p" ('a', Var "x" :: Var Char)]
  describe "the \"get solutions\" feature" $ do
    it "should return the theorem at the root of a proof tree" $ do
      getSolution (Proof ( PredGoal $ predicate "p" ())
                         [ Proof (PredGoal $ predicate "q" () ) [Axiom $ PredGoal $ predicate "r" ()]
                         , Axiom (PredGoal $ predicate "s" ())
                         ], mempty) `shouldBe`
        predicate "p" ()
      getSolution (Axiom $ PredGoal $ predicate "p" (), mempty) `shouldBe` predicate "p" ()
    it "should get all solutions from a forest of proof tress" $
      getAllSolutions [ (Axiom $ PredGoal $ predicate "p" (), mempty)
                      , (Axiom $ PredGoal $ predicate "q" (), mempty)] `shouldBe`
        [predicate "p" (), predicate "q" ()]
  describe "the \"get unifiers\" feature" $ do
    it "should return the unifier from a solution" $ do
      let u = toTerm 'a' // Var "x" <> toTerm True // Var "y"
      getUnifier (Axiom $ PredGoal $ predicate "foo" (), u) `shouldBe` u
    it "should return all unifiers from a solution forest" $ do
      let u1 = toTerm 'a' // Var "x"
      let u2 = toTerm True // Var "y"
      getAllUnifiers [ (Axiom $ PredGoal $ predicate "foo" (), u1)
                     , (Axiom $ PredGoal $ predicate "bar" (), u2)] `shouldBe`
        [u1, u2]
  describe "the HSPL solver" $ do
    it "should return all proofs of the query" $ do
      let (proofs, _) = unzip $ runHspl syllogism (predicate "mortal" "hypatia")
      proofs `shouldBe` [Proof (PredGoal $ predicate "mortal" "hypatia")
                               [Axiom $ PredGoal $ predicate "human" "hypatia"]]
      let (proofs2, _) = unzip $ runHspl syllogism (predicate "mortal" (Var "x" :: Var String))
      proofs2 `shouldBePermutationOf`
        [ Proof (PredGoal $ predicate "mortal" "hypatia") [Axiom (PredGoal $ predicate "human" "hypatia")]
        , Proof (PredGoal $ predicate "mortal" "fred") [Axiom (PredGoal $ predicate "human" "fred")]
        ]
    it "should return the requested number of proofs" $ do
      let (proofs, _) = unzip $ runHsplN 1 syllogism $ predicate "mortal" (Var "x" :: Var String)
      proofs `shouldBeSubsetOf`
        [ Proof (PredGoal $ predicate "mortal" "hypatia") [Axiom $ PredGoal $ predicate "human" "hypatia"]
        , Proof (PredGoal $ predicate "mortal" "fred") [Axiom $ PredGoal $ predicate "human" "fred"]
        ]
      length proofs `shouldBe` 1
    it "should handle a proof with multiple subgoals" $ do
      let (proofs, _) = unzip $ runHspl example1 (predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
      proofs `shouldBe` [Proof ( PredGoal $ predicate "foo" ('a', 'b'))
                               [ Axiom $ PredGoal $ predicate "bar" 'a'
                               , Axiom $ PredGoal $ predicate "baz" 'b']
                        ]
    it "should indicate when variables have been substituted" $ do
      let (_, us) = unzip $ runHspl memberProgram (predicate "member" (Var "x" :: Var Int, [1 :: Int]))
      length us `shouldBe` 1
      head us `shouldSatisfy` (((1 :: Int) // Var "x") `isSubunifierOf`)
    it "should return a unifier for each solution" $ do
      let (_, us) = unzip $ runHspl syllogism (predicate "mortal" (Var "x" :: Var String))
      length us `shouldBe` 2
      if head us `isSubunifierOf` ("hypatia" // Var "x")
        then last us `shouldSatisfy` (("fred" // Var "x") `isSubunifierOf`)
        else do head us `shouldSatisfy` (("fred" // Var "x") `isSubunifierOf`)
                last us `shouldSatisfy` (("hypatia" // Var "x") `isSubunifierOf`)
    it "should handle multiple variables" $ do
      let (_, us) = unzip $ runHspl example0 (predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
      length us `shouldBe` 1
      head us `shouldSatisfy` (('a' // Var "x" <> 'b' // Var "y") `isSubunifierOf`)
    it "should prove a successful CanUnify" $ do
      let fooProof = Proof (PredGoal $ predicate "isFoo" "foo")
                           [Axiom $ CanUnify (toTerm "foo") (toTerm "foo")]
      let (proofs, _) = unzip $ runHspl canUnify (predicate "isFoo" "foo")
      proofs `shouldBe` [fooProof]
      let (proofs', _) = unzip $ runHspl canUnify (predicate "isFoo" (Var "x" :: Var String))
      proofs' `shouldBe` [fooProof]
    it "should fail an unsuccessful CanUnify" $
      runHspl canUnify (predicate "isFoo" "bar") `shouldBe` []
