{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraints
{-# LANGUAGE TypeSynonymInstances #-}

module SolverTest where

import Testing
import Control.Applicative
import Control.DeepSeq (NFData (..))
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.Unification
import Control.Monad (liftM2)
import Control.Monad.IO.Class
import Data.Monoid hiding (Sum, Product)
import Data.Typeable

instance NFData ProofResult where
  rnf ProofResult {..} = mainTheorem `seq` trackedTheorems `seq` rnf unifiedVars

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

observeResults m = observeAllSolver (m >>= getResult) ()

test = describeModule "Control.Hspl.Internal.Solver" $ do
  describe "provePredicate" $ do
    let runTest p c = observeResults $ provePredicate p c
    it "should prove an axiom" $
      getAllTheorems (runTest (predicate "foo" ('a', 'b')) simpleBinary) `shouldBe`
        [PredGoal (predicate "foo" ('a', 'b')) [simpleBinary]]
    it "should prove a result that follows from a subgoal" $ do
      let results = runTest (predicate "mortal" "hypatia") mortal
      getAllTheorems results `shouldBe` [PredGoal (predicate "mortal" "hypatia") []]
    it "should return unifications made in the goal" $ do
      let us = runTest (predicate "foo" (Var "x" :: Var Char)) simpleSubGoal
      length us `shouldBe` 1
      queryVar (head us) (Var "x") `shouldBe` Unified 'a'
  describe "proveUnifiable" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> [ProofResult]
        runTest t1 t2 = observeResults $ proveUnifiable (toTerm t1) (toTerm t2)
    it "should unify terms when possible" $ do
      let results = runTest (Var "x" :: Var String) "foo"
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe` CanUnify (toTerm "foo") (toTerm "foo")
      queryVar (head results) (Var "x") `shouldBe` Unified "foo"
    it "should fail when terms cannot be unified" $
      runTest "bar" "foo" `shouldBe` []
  describe "proveIdentical" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> [ProofResult]
        runTest t1 t2 = observeResults $ proveIdentical (toTerm t1) (toTerm t2)
    it "should fail if the terms are not equal" $
      runTest "foo" "bar" `shouldBe` []
    it "should fail if the terms are not yet unified" $
      runTest (Var "x" :: Var String) "foo" `shouldBe` []
    it "should succeed, but not create new bindings, if the terms are identical" $
      getAllTheorems (runTest "foo" "foo") `shouldBe` [Identical (toTerm "foo") (toTerm "foo")]
  describe "proveEqual" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> [ProofResult]
        runTest lhs rhs = observeResults $ proveEqual (toTerm lhs) (toTerm rhs)
    it "should unify a variable with a constant" $ do
      let results = runTest (Var "x" :: Var Int) (1 :: Int)
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe` Equal (toTerm (1 :: Int)) (toTerm (1 :: Int))
      queryVar (head results) (Var "x") `shouldBe` Unified (1 :: Int)
    it "should evaluate an arithmetic expression" $ do
      let results = runTest (5 :: Int) (Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))
      getAllTheorems results `shouldBe` [Equal (toTerm (5 :: Int)) (toTerm (5 :: Int))]
    it "should evaluate arithmetic sub-expressions" $ do
      let lhs = toTerm $ Just (5 :: Int)
      let rhs = adt Just $ Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))
      getAllTheorems (runTest lhs rhs) `shouldBe` [Equal lhs lhs]
    it "should evaluate and unify sub-expressions" $ do
      let rhs = adt Just $ Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))
      let results = runTest (adt Just (Var "x" :: Var Int)) rhs
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe` Equal (toTerm $ Just (5 :: Int)) (toTerm $ Just (5 :: Int))
      queryVar (head results) (Var "x") `shouldBe` Unified (5 :: Int)
    it "should fail when the left-hand side does not unify with the result of the right" $
      runTest (5 :: Int) (Product (toTerm (3 :: Int)) (toTerm (2 :: Int))) `shouldBe` []
    it "should error when the right-hand side contains uninstantiated variables" $
      assertError uninstantiatedVariablesError $
        runTest (Var "x" :: Var Int) (Sum (toTerm (42 :: Int)) (toTerm (Var "y" :: Var Int)))
  describe "proveLessThan" $ do
    let runTest :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
                   a -> b -> [ProofResult]
        runTest lhs rhs = observeResults $ proveLessThan (toTerm lhs) (toTerm rhs)
    it "should succeed when the left-hand side is less than the right-hand side" $
      getAllTheorems (runTest 'a' 'b') `shouldBe` [LessThan (toTerm 'a') (toTerm 'b')]
    it "should simplify terms before comparing" $ do
      let results = runTest (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                            (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
      getAllTheorems results `shouldBe` [LessThan (toTerm (5 :: Int)) (toTerm (6 :: Int))]
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
  describe "proveIsUnified" $ do
    it "should succeed for fully instantiated terms" $ do
      let runTest t = getAllTheorems (observeResults $ proveIsUnified $ toTerm t) `shouldBe`
                        [IsUnified $ toTerm t]
      runTest 'a'
      runTest $ Just 'a'
      runTest (Nothing :: Maybe Char)
      runTest "foo"
      runTest ('a', 'b')
      runTest $ Sum (toTerm (0 :: Int)) (toTerm (1 :: Int))
    it "should fail for variables" $ do
      let runTest t = observeResults (proveIsUnified $ toTerm t) `shouldBe` []
      runTest (Var "x" :: Var Char)
      runTest (Fresh 0 :: Var Char)
    it "should fail for partially instantiated terms" $ do
      let runTest t = observeResults (proveIsUnified $ toTerm t) `shouldBe` []
      runTest $ adt Just (Var "x" :: Var Char)
      runTest $ List $ VarCons (toTerm 'a') (Var "xs")
      runTest ('a', Var "x" :: Var Char)
      runTest $ Sum (toTerm (0 :: Int)) (toTerm $ Var "x")
  describe "proveIsVariable" $ do
    it "should succeed for variables" $ do
      let runTest t = getAllTheorems (observeResults (proveIsVariable $ toTerm t)) `shouldBe`
            [IsVariable $ toTerm t]
      runTest (Var "x" :: Var Char)
      runTest (Fresh 0 :: Var Char)
    it "should fail for fully instantiated terms" $ do
      let runTest t = observeResults (proveIsVariable $ toTerm t) `shouldBe` []
      runTest 'a'
      runTest $ Just 'a'
      runTest (Nothing :: Maybe Char)
      runTest "foo"
      runTest ('a', 'b')
      runTest $ Sum (toTerm (0 :: Int)) (toTerm (1 :: Int))
    it "should fail for partially instantiated terms" $ do
      let runTest t = observeResults (proveIsVariable $ toTerm t) `shouldBe` []
      runTest $ adt Just (Var "x" :: Var Char)
      runTest $ List $ VarCons (toTerm 'a') (Var "xs")
      runTest ('a', Var "x" :: Var Char)
      runTest $ Sum (toTerm (0 :: Int)) (toTerm $ Var "x")
  describe "proveNot" $ do
    let runTest g = observeResults $ proveNot g
    it "should fail if the inner goal succeeds" $
      runTest (PredGoal (predicate "foo" ('a', 'b')) [simpleBinary]) `shouldBe` []
    it "should succeed if the inner goal fails" $
      getAllTheorems (runTest $ PredGoal (predicate "foo" ('b', 'a')) [simpleBinary]) `shouldBe`
        [Not $ PredGoal (predicate "foo" ('b', 'a')) [simpleBinary]]
  describe "proveAnd" $ do
    let runTest g1 g2 = observeResults $ proveAnd g1 g2
    it "should succeed when both subgoals succeed" $ do
      let results = runTest (Identical (toTerm 'a') (toTerm 'a'))
                            (Identical (toTerm 'b') (toTerm 'b'))
      getAllTheorems results `shouldBe` [And (Identical (toTerm 'a') (toTerm 'a'))
                                             (Identical (toTerm 'b') (toTerm 'b'))]
    it "should fail when the left subgoal fails" $
      runTest (Identical (toTerm 'a') (toTerm 'b')) (Identical (toTerm 'c') (toTerm 'c')) `shouldBe`
        []
    it "should fail when the right subgoal fails" $
      runTest (Identical (toTerm 'a') (toTerm 'a')) (Identical (toTerm 'b') (toTerm 'c')) `shouldBe`
        []
    it "should return any unifications made in either goal" $ do
      let results = runTest (CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char)))
                            (CanUnify (toTerm (Var "y" :: Var Bool)) (toTerm True))
      length results `shouldBe` 1
      queryVar (head results) (Var "x") `shouldBe` Unified 'a'
      queryVar (head results) (Var "y") `shouldBe` Unified True
    it "should apply unifications made while proving the left-hand side to the right-hand side" $
      runTest (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'a'))
              (CanUnify (toTerm 'b') (toTerm (Var "x" :: Var Char))) `shouldBe` []
  describe "an Or goal" $ do
    let runTest g1 g2 = observeResults $ prove $ Or g1 g2
    it "should succeed when only the left goal succeeds" $ do
      -- Left goal succeeds once, right goal fails
      let results = runTest (PredGoal (predicate "mortal" "hypatia") [mortal])
                            (PredGoal (predicate "fake" ()) [])
      getAllTheorems results `shouldBe` [Or (PredGoal (predicate "mortal" "hypatia") [])
                                            (PredGoal (predicate "fake" ()) [])]
      -- Left goals succeeds multiple times, right goal fails
      let results = runTest (PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal])
                            (PredGoal (predicate "fake" ()) [])
      length results `shouldBe` 2
      getAllTheorems results `shouldBe` [ Or (PredGoal (predicate "mortal" "hypatia") [])
                                             (PredGoal (predicate "fake" ()) [])
                                        , Or (PredGoal (predicate "mortal" "fred") [])
                                             (PredGoal (predicate "fake" ()) [])
                                        ]
      if queryVar (head results) (Var "x") == Unified "hypatia"
        then queryVar (last results) (Var "x") `shouldBe` Unified "fred"
        else do queryVar (head results) (Var "x") `shouldBe` Unified "fred"
                queryVar (last results) (Var "x") `shouldBe` Unified "hypatia"
    it "should succeed when only the right goal succeeds" $ do
      -- Right goal succeeds once, left goal fails
      let results = runTest (PredGoal (predicate "fake" ()) [])
                            (PredGoal (predicate "mortal" "hypatia") [mortal])
      getAllTheorems results `shouldBe` [Or (PredGoal (predicate "fake" ()) [])
                                            (PredGoal (predicate "mortal" "hypatia") [])]
      -- Left goals succeeds multiple times, right goal fails
      let results = runTest (PredGoal (predicate "fake" ()) [])
                            (PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal])
      length results `shouldBe` 2
      getAllTheorems results `shouldBe` [ Or (PredGoal (predicate "fake" ()) [])
                                             (PredGoal (predicate "mortal" "hypatia") [])
                                        , Or (PredGoal (predicate "fake" ()) [])
                                             (PredGoal (predicate "mortal" "fred") [])
                                        ]
      if queryVar (head results) (Var "x") == Unified "hypatia"
        then queryVar (last results) (Var "x") `shouldBe` Unified "fred"
        else do queryVar (head results) (Var "x") `shouldBe` Unified "fred"
                queryVar (last results) (Var "x") `shouldBe` Unified "hypatia"
    it "should succeed once for each subgoal that succeeds" $ do
      let results = runTest (PredGoal (predicate "mortal" "hypatia") [mortal])
                            (PredGoal (predicate "mortal" "fred") [mortal])
      getAllTheorems results `shouldBe` [ Or (PredGoal (predicate "mortal" "hypatia") [mortal])
                                             (PredGoal (predicate "mortal" "fred") [mortal])
                                        , Or (PredGoal (predicate "mortal" "hypatia") [mortal])
                                             (PredGoal (predicate "mortal" "fred") [mortal])
                                        ]
    it "should fail when both goals fail" $
      runTest (PredGoal (predicate "fake" ()) []) (PredGoal (predicate "fake" ()) []) `shouldBe` []
  describe "proveTop" $
    it "should always succeed" $
      getAllTheorems (observeResults proveTop) `shouldBe` [Top]
  describe "proveBottom" $
    it "should always fail" $
      observeResults proveBottom `shouldBe` []
  describe "proveCut" $ do
    let runTest g = observeResults $ prove g
    it "should discard choicepoints created since the last predicate" $
      getAllTheorems (runTest (Or Cut Top)) `shouldBe` [Or Cut Top]
    it "should not discard choiceoints created after the last predicate" $ do
      let p = PredGoal (predicate "foo" ()) [ HornClause (predicate "foo" ()) Cut
                                            , HornClause (predicate "foo" ()) Top
                                            ]
      getAllTheorems (runTest (Or p (CanUnify (toTerm 'a') (toTerm 'a')))) `shouldBe`
        [ Or (PredGoal (predicate "foo" ()) [])
             (CanUnify (toTerm 'a') (toTerm 'a'))
        , Or (PredGoal (predicate "foo" ()) [])
             (CanUnify (toTerm 'a') (toTerm 'a'))
        ]
    it "should prevent side-effects in unexplored branches" $
      tempFile $ \f -> do
        observeAllSolverT (proveCut <|> (liftIO (writeFile f "foo") >> proveTop)) ()
        output <- readFile f
        output `shouldBe` ""
  describe "proveCutFrame" $ do
    let runTest g = observeResults $ proveCutFrame g
    it "should fail when the inner goal fails" $
      runTest Bottom `shouldBe` []
    it "should succeed when the inner goal succeeds" $ do
      getAllTheorems (runTest Top) `shouldBe` [CutFrame Top]
      getAllTheorems (runTest $ Or Top Top) `shouldBe` replicate 2 (CutFrame $ Or Top Top)
    it "should save choicepoints" $
      length (getAllTheorems $ observeResults $ prove $ Or (CutFrame $ Or Cut Top) Top) `shouldBe` 2
  describe "an Alternatives proof" $ do
    let runTest x g xs = observeResults $ proveAlternatives Nothing x g xs
    let xIsAOrB = Or (Track $ CanUnify (toTerm $ Var "x") (toTerm 'a'))
                     (Track $ CanUnify (toTerm $ Var "x") (toTerm 'b'))
    let x :: Term Char
        x = toTerm $ Var "x"
        xs :: Term [Char]
        xs = toTerm $ Var "xs"
    it "should unify a variable with a list of alternatives" $ do
      let results = runTest x xIsAOrB xs
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe` Alternatives Nothing x xIsAOrB (toTerm ['a', 'b'])
      queryVar (head results) (Var "x" :: Var Char) `shouldBe` Ununified
      queryVar (head results) (Var "xs") `shouldBe` Unified "ab"
    it "should succeed even if the inner goal fails" $ do
      let results = runTest x Bottom xs
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe` Alternatives Nothing x Bottom (List Nil)
      queryVar (head results) (Var "xs" :: Var String) `shouldBe` Unified []
    it "should fail if the output term does not unify with the alternatives" $ do
      runTest x xIsAOrB (toTerm [Var "y" :: Var Char]) `shouldBe` []
      runTest x Bottom (List $ VarCons (toTerm (Var "y" :: Var Char)) (Var "ys")) `shouldBe` []
    it "should handle complex templates" $ do
      let results = runTest (adt Just x) xIsAOrB (toTerm (Var "xs" :: Var [Maybe Char]))
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe`
        Alternatives Nothing (adt Just x) xIsAOrB (toTerm [Just 'a', Just 'b'])
      queryVar (head results) (Var "xs") `shouldBe` Unified [Just 'a', Just 'b']
    it "should take place in the same environment as the parent goal" $ do
      let g = PredGoal (predicate "foo" 'a')
                       [HornClause (predicate "foo" (Var "x" :: Var Char))
                                   (Track $ Alternatives Nothing
                                              (toTerm (Var "y" :: Var Char))
                                              (Equal (toTerm (Var "y" :: Var Char)) (toTerm $ Var "x"))
                                              (toTerm [Var "x"]))
                       ]
      let results = runHspl g
      length results `shouldBe` 1
      case queryTheorem (head results) (Alternatives Nothing
                                          (toTerm (Var "x" :: Var Char))
                                          (Equal (toTerm (Var "l" :: Var Char))
                                                 (toTerm $ Var "r"))
                                          (toTerm (Var "xs"))) of
        [Alternatives Nothing x g xs] -> do
          case cast x of
            Just (x' :: Term Char) -> x' `shouldBeAlphaEquivalentTo` (Var "y" :: Var Char)
            Nothing -> failure $ "Expected y :: Char, but got " ++ show x
          case cast xs of
            Just xs' -> xs' `shouldBe` toTerm ['a']
            Nothing -> failure $ "Expected ['a'], but got " ++ show xs
          case g of
            Equal t1 t2 -> do
              case cast t1 of
                Just (t1' :: Term Char) -> t1' `shouldBeAlphaEquivalentTo` (Var "y" :: Var Char)
                Nothing -> failure $ "Expected y :: Char, but got " ++ show t1
              case cast t2 of
                Just t2' -> t2' `shouldBe` toTerm 'a'
                Nothing -> failure $ "Expected 'a', but got " ++ show t2
            _ -> failure $ "Expected Equal y 'a', but got " ++ show g

        thms -> failure $ "Expected [Alternatives y (Equal y 'a') ['a']], but got " ++ show thms
    it "should return proofs of each alternative" $ do
      let results = runTest x xIsAOrB xs
      length results `shouldBe` 1
      queryTheorem (head results) (CanUnify (toTerm (Var "l" :: Var Char)) (toTerm $ Var "r"))
        `shouldBePermutationOf` [CanUnify (toTerm 'a') (toTerm 'a'), CanUnify (toTerm 'b') (toTerm 'b')]
    it "should return a requested number of results" $ do
      let results = runHspl $ Alternatives (Just 1) x xIsAOrB xs
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe` Alternatives (Just 1) x xIsAOrB (toTerm "a")
      queryVar (head results) (Var "xs") `shouldBe` Unified "a"
    when "the template variable is already bound" $
      it "should return a list of the bound variable" $ do
        let results = runHspl $ CanUnify (toTerm $ Var "y") (toTerm 'c') <>
                                Alternatives Nothing (toTerm $ Var "y") xIsAOrB xs
        length results `shouldBe` 1
        getTheorem (head results) `shouldBe` And (CanUnify (toTerm 'c') (toTerm 'c'))
                                                 (Alternatives Nothing (toTerm 'c') xIsAOrB (toTerm ['c', 'c']))
        queryVar (head results) (Var "xs") `shouldBe` Unified ['c', 'c']
    when "the template variable is unbound" $
      it "should return a list of variables" $ do
        let results = runTest x Top xs
        length results `shouldBe` 1
        getTheorem (head results) `shouldBe` Alternatives Nothing x Top (toTerm [x])
        queryVar (head results) (Var "xs") `shouldBe` Partial (toTerm [x])
  describe "proveTrack" $ do
    let runTest g = observeResults $ proveTrack g
    it "should fail if the inner goal fails" $
      runTest Bottom `shouldBe` []
    it "should succeed once for each time the inner goal succeeds" $ do
      getAllTheorems (runTest Top) `shouldBe` [Track Top]
      getAllTheorems (runTest $ Or Top Top) `shouldBe` [Track $ Or Top Top, Track $ Or Top Top]
    it "should emit a searchable proof of the inner goal" $ do
      let results = runTest Top
      length results `shouldBe` 1
      queryTheorem (head results) Top `shouldBe` [Top]
  describe "a proof search" $ do
    it "should find goals which unify with a target goal" $
      queryTheorem (ProofResult (IsUnified $ toTerm 'a') [IsUnified $ toTerm 'a', IsUnified $ toTerm 'b'] mempty)
                   (IsUnified (toTerm (Var "x" :: Var Char))) `shouldBe`
        [IsUnified $ toTerm 'a', IsUnified $ toTerm 'b']
    it "should unify proven theorems using the final unifier" $
      queryTheorem (ProofResult Top [CanUnify (toTerm $ Var "x") (toTerm 'a')] ('a' // Var "x"))
                   (CanUnify (toTerm (Var "l" :: Var Char)) (toTerm $ Var "r")) `shouldBe`
        [CanUnify (toTerm 'a') (toTerm 'a')]
    let shouldMatch patt goal =
          do queryTheorem (ProofResult Top [patt] mempty) goal `shouldBe` [goal]
             queryTheorem (ProofResult Top [goal] mempty) patt `shouldBe` [goal]
    let shouldNotMatch patt goal =
          do queryTheorem (ProofResult Top [patt] mempty) goal `shouldBe` []
             queryTheorem (ProofResult Top [goal] mempty) patt `shouldBe` []
    context "for a predicate goal" $ do
      it "should match when the names are the same and the arguments unify" $
        PredGoal (predicate "foo" (Var "x" :: Var Char)) [] `shouldMatch`
          PredGoal (predicate "foo" 'a') []
      it "should not match when the names are different" $
        PredGoal (predicate "foo" 'a') [] `shouldNotMatch` PredGoal (predicate "bar" 'a') []
      it "should not match when the arguments don't unify" $
        PredGoal (predicate "foo" 'a') [] `shouldNotMatch` PredGoal (predicate "foo" 'b') []
    withParams [CanUnify, Identical, Equal, LessThan] $ \g ->
      context "for a binary term goal" $ do
        it "should match when the arguments unify" $ do
          g (toTerm (Var "l" :: Var Char)) (toTerm $ Var "r") `shouldMatch` g (toTerm 'a') (toTerm 'b')
          g (toTerm 'a') (toTerm 'b') `shouldMatch` g (toTerm 'a') (toTerm 'b')
        it "should not match when the arguemtns don't unify" $ do
          g (toTerm 'a') (toTerm 'b') `shouldNotMatch` g (toTerm 'a') (toTerm 'a')
          g (toTerm 'a') (toTerm 'b') `shouldNotMatch` g (toTerm 'b') (toTerm 'b')
    withParams [IsUnified, IsVariable] $ \g ->
      context "for a unary term goal" $ do
        it "should match when the arguments unify" $ do
          g (toTerm (Var "x" :: Var Char)) `shouldMatch` g (toTerm 'a')
          g (toTerm 'a') `shouldMatch` g (toTerm 'a')
        it "should not match when the arguemtns don't unify" $
          g (toTerm 'a') `shouldNotMatch` g (toTerm 'b')
    withParams [And, Or] $ \g ->
      context "for binary subgoals" $ do
        it "should match when the arguments match" $
          g Top Bottom `shouldMatch` g Top Bottom
        it "should not match when the arguments don't match" $ do
          g Top Bottom `shouldNotMatch` g Top Top
          g Top Bottom `shouldNotMatch` g Bottom Bottom
    withParams [Not, CutFrame, Track] $ \g ->
      context "for unary subgoals" $ do
        it "should match when the arguments match" $
          g Top `shouldMatch` g Top
        it "should not match when the arguments don't match" $
          g Top `shouldNotMatch` g Bottom
    withParams [Top, Bottom, Cut] $ \g ->
      context "for a unitary goal" $
        it "should match" $
          g `shouldMatch` g
    context "for an alternatives goal" $ do
      withParams [Nothing, Just 42] $ \n ->
        it "should match when the arguments match" $
          Alternatives n (toTerm (Var "x" :: Var Char)) Top (toTerm $ Var "xs") `shouldMatch`
            Alternatives n (toTerm 'a') Top (toTerm "foo")
      it "should not match when the arguments don't match" $ do
        Alternatives Nothing (toTerm 'a') Top (toTerm "foo") `shouldNotMatch`
          Alternatives Nothing (toTerm 'b') Top (toTerm "foo")
        Alternatives Nothing (toTerm 'a') Top (toTerm "foo") `shouldNotMatch`
          Alternatives Nothing (toTerm 'a') Cut (toTerm "foo")
        Alternatives Nothing (toTerm 'a') Top (toTerm "foo") `shouldNotMatch`
          Alternatives Nothing (toTerm 'a') Top (toTerm "bar")
        Alternatives Nothing (toTerm 'a') Top (toTerm "foo") `shouldNotMatch`
          Alternatives (Just 42) (toTerm 'a') Top (toTerm "foo")

  describe "the \"get theorems\" feature" $ do
    it "should return the theorem at the root of a proof tree" $
      getTheorem (ProofResult Top [Bottom] mempty) `shouldBe` Top
    it "should unify the theorem with the final unifier" $
      getTheorem (ProofResult (CanUnify (toTerm $ Var "x") (toTerm 'a')) [] ('a' // Var "x")) `shouldBe`
        CanUnify (toTerm 'a') (toTerm 'a')
    it "should get all theorems from a forest of proof tress" $
      getAllTheorems [ ProofResult Top [] mempty, ProofResult Cut [] mempty] `shouldBe` [Top, Cut]
  describe "the HSPL solver" $ do
    it "should return all proofs of the query" $ do
      let results = runHspl $ PredGoal (predicate "mortal" "hypatia") [mortal]
      getAllTheorems results `shouldBe` [PredGoal (predicate "mortal" "hypatia") [mortal]]

      let results = runHspl $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      getAllTheorems results `shouldBe`
        [ PredGoal (predicate "mortal" "hypatia") [mortal]
        , PredGoal (predicate "mortal" "fred") [mortal]
        ]
    it "should return the requested number of proofs" $ do
      let results = runHsplN 1 $ PredGoal (predicate "mortal" (Var "x" :: Var String)) [mortal]
      getAllTheorems results `shouldBe` [PredGoal (predicate "mortal" "hypatia") [mortal]]
