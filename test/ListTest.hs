{-# LANGUAGE CPP #-}
module ListTest where

import Testing
import Control.Hspl
import qualified Control.Hspl.List as L
import Control.Hspl.Internal.Ast
import qualified Control.Hspl.Internal.Ast as Ast
import Control.Hspl.Internal.Syntax

import Control.Monad
import Data.CallStack
import Data.Maybe
import Data.Monoid

test = describeModule "Control.Hspl.List" $ do
  describe "the length predicate" $ do
    it "should succeed when given the correct length of a list" $ do
      length (getAllTheorems $ runHspl $ L.length? ([] :: [Char], 0 :: Int)) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.length? (['a', 'b', 'c'], 3 :: Int)) `shouldBe` 1
    it "should fail when given the incorrect length of a list" $ do
      getAllTheorems (runHspl $ L.length? ([] :: [Char], 1 :: Int)) `shouldBe` []
      getAllTheorems (runHspl $ L.length? (['a', 'b', 'c'], 2 :: Int)) `shouldBe` []
    it "should compute the length of a list" $ do
      let us = runHspl $ L.length? ([] :: [Char], int "L")
      length us `shouldBe` 1
      queryVar (head us) (int "L") `shouldBe` Unified (0 :: Int)

      let us = runHspl $ L.length? (['a', 'b', 'c'], int "L")
      length us `shouldBe` 1
      queryVar (head us) (int "L") `shouldBe` Unified (3 :: Int)
    it "should generate lists of increasing length" $ do
      let us = runHsplN 3 $ L.length? (string "xs", int "L")
      length us `shouldBe` 3

      queryVar (head us) (string "xs") `shouldBe` Unified []
      queryVar (head us) (int "L") `shouldBe` Unified 0

      case queryVar (us !! 1) (string "xs") of
        Partial t -> t `shouldBeAlphaEquivalentTo` [Fresh 0 :: Var Char]
        st -> fail $ "Expected [_0], but found " ++ show st
      queryVar (us !! 1) (int "L") `shouldBe` Unified 1

      case queryVar (us !! 2) (string "xs") of
        Partial t -> t `shouldBeAlphaEquivalentTo` [Fresh 0 :: Var Char, Fresh 1 :: Var Char]
        st -> fail $ "Expected [_0, _1], but found " ++ show st
      queryVar (us !! 2) (int "L") `shouldBe` Unified 2
    it "should generate lists of increasing length from a partial list" $ do
      let us = runHsplN 3 $ L.length? ('a' .:. v"xs", int "L")
      length us `shouldBe` 3

      queryVar (head us) (string "xs") `shouldBe` Unified []
      queryVar (head us) (int "L") `shouldBe` Unified 1

      case queryVar (us !! 1) (string "xs") of
        Partial t -> t `shouldBeAlphaEquivalentTo` [Fresh 0 :: Var Char]
        st -> fail $ "Expected [_0], but found " ++ show st
      queryVar (us !! 1) (int "L") `shouldBe` Unified 2

      case queryVar (us !! 2) (string "xs") of
        Partial t -> t `shouldBeAlphaEquivalentTo` [Fresh 0 :: Var Char, Fresh 1 :: Var Char]
        st -> fail $ "Expected [_0, _1], but found " ++ show st
      queryVar (us !! 2) (int "L") `shouldBe` Unified 3

  describe "the member predicate" $ do
    it "should succeed when given an element of the list" $ do
      length (getAllTheorems $ runHspl $ L.member? ('a', ['a', 'b', 'c'])) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.member? ('b', ['a', 'b', 'c'])) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.member? ('c', ['a', 'b', 'c'])) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.member? ('a', ['a', 'b', 'a', 'c'])) `shouldBe` 2
    it "should fail when given a value that is not in the list" $ do
      getAllTheorems (runHspl $ L.member? ('a', ['b', 'c', 'd'])) `shouldBe` []
      getAllTheorems (runHspl $ L.member? ('a', [] :: [Char])) `shouldBe` []
    it "should backtrack over all elements of the list" $ do
      let us = runHspl $ L.member? (char "x", ['a', 'b', 'c'])
      length us `shouldBe` 3

      queryVar (us !! 0) (char "x") `shouldBe` Unified 'a'
      queryVar (us !! 1) (char "x") `shouldBe` Unified 'b'
      queryVar (us !! 2) (char "x") `shouldBe` Unified 'c'
    it "should generate lists with the given element" $ do
      let us = runHsplN 3 $ L.member? ('a', string "xs")
      length us `shouldBe` 3
      forM_ [0..length us - 1] $ \n ->
        case queryVar (us !! n) (string "xs") of
          Partial t -> t `shouldBeAlphaEquivalentTo`
            (([toTerm $ Fresh i | i <- [0..n-1]] ++ [toTerm 'a']) .++. Fresh n)
          st -> failure $ "Expected Partial but got " ++ show st
    it "should generate partial list tails with the given element" $ do
      let us = runHsplN 3 $ L.member? ('b', 'a' .:. v"xs")
      length us `shouldBe` 3
      forM_ [0..length us - 1] $ \n ->
        case queryVar (us !! n) (string "xs") of
          Partial t -> t `shouldBeAlphaEquivalentTo`
            (([toTerm $ Fresh i | i <- [0..n-1]] ++ [toTerm 'b']) .++. Fresh n)
          st -> failure $ "Expected Partial but got " ++ show st

  describe "the nth predicate" $ do
    it "should succeed when given the correct index and element" $ do
      length (getAllTheorems $ runHspl $ L.nth? (0 :: Int, ['a', 'b', 'c'], 'a')) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.nth? (1 :: Int, ['a', 'b', 'c'], 'b')) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.nth? (2 :: Int, ['a', 'b', 'c'], 'c')) `shouldBe` 1
    it "should fail when given the incorrect index and element" $ do
      getAllTheorems (runHspl $ L.nth? (0 :: Int, [] :: [Char], 'a')) `shouldBe` []
      getAllTheorems (runHspl $ L.nth? (0 :: Int, ['a', 'b'], 'b')) `shouldBe` []
      getAllTheorems (runHspl $ L.nth? (1 :: Int, ['a', 'b'], 'a')) `shouldBe` []
    it "should calculate the index of an element" $ do
      let us = runHspl $ L.nth? (int "i", ['a', 'b', 'a'], 'a')
      length us `shouldBe` 2
      queryVar (head us) (int "i") `shouldBe` Unified 0
      queryVar (last us) (int "i") `shouldBe` Unified 2

      let us = runHspl $ L.nth? (int "i", ['a', 'b', 'a'], 'b')
      length us `shouldBe` 1
      queryVar (head us) (int "i") `shouldBe` Unified 1
    withParams ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg"] $ \l ->
      withParams [0..length l - 1] $ \n ->
        it "should calculate the element at a given position" $ do
          let us = runHspl $ L.nth? (n, l, char "c")
          length us `shouldBe` 1
          queryVar (head us) (char "c") `shouldBe` Unified (l !! n)
    it "should enumerate a list" $ do
      let us = runHspl $ L.nth?(int "i", ['a', 'b'], char "c")
      length us `shouldBe` 2
      queryVar (head us) (int "i") `shouldBe` Unified 0
      queryVar (last us) (int "i") `shouldBe` Unified 1
    it "should insert an element in a list" $ do
      let us = runHspl $ L.nth?(0 :: Int, [char "x", char "y"], 'a')
      length us `shouldBe` 1
      queryVar (head us) (char "x") `shouldBe` Unified 'a'

      let us = runHspl $ L.nth?(1 :: Int, [char "x", char "y"], 'a')
      length us `shouldBe` 1
      queryVar (head us) (char "y") `shouldBe` Unified 'a'
    it "should generate successively longer lists with an element at a given position" $ do
      let us = runHsplN 3 $ L.nth? (int "n", string "l", 'a')
      length us `shouldBe` 3
      forM_ [0..length us - 1] $ \n -> do
        let u = us !! n
        queryVar u (int "n") `shouldBe` Unified n
        case queryVar u (string "l") of
          Partial l -> l `shouldBeAlphaEquivalentTo`
            ((map (toTerm.Fresh) [0..n-1] ++ [toTerm 'a']) .++. Fresh n)
          st -> failure $ "Expected Partial but got " ++ show st

  describe "the delete predicate" $ do
    withParams [[], ['a', 'b'], ['a', 'a', 'c'], ['a', 'b', 'b', 'a'], ['b', 'b']] $ \l ->
      it "should delete all occurrences of an element from a list" $ do
        let us = runHspl $ L.delete? (l, 'b', v"xs")
        let expected = [x | x <- l, x /= 'b']
        length us `shouldBe` 1
        queryVar (head us) (v"xs") `shouldBe` Unified expected
    it "should succeed when given the deleted list" $ do
      length (getAllTheorems $ runHspl $ L.delete? (nil, 'b', nil)) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.delete? (['b'], 'b', nil)) `shouldBe` 1
      length (getAllTheorems $ runHspl $ L.delete? (['a', 'b'], 'b', ['a'])) `shouldBe` 1
    it "should fail when given a list that does not unify with the deleted list" $ do
      length (getAllTheorems $ runHspl $ L.delete? (nil, 'b', v"x" .:. v"xs")) `shouldBe` 0
      length (getAllTheorems $ runHspl $ L.delete? (['b'], 'b', ['b'])) `shouldBe` 0
      length (getAllTheorems $ runHspl $ L.delete? (['a', 'b'], 'b', ['a', 'b'])) `shouldBe` 0
      length (getAllTheorems $ runHspl $ L.delete? (['a', 'b'], 'b', ['a', 'c'])) `shouldBe` 0

  describe "predicate scoping" $ do
    let runTest :: Ast.Predicate -> Expectation
        runTest (Predicate loc scope _ _) = do
#if MIN_VERSION_base(4,8,1)
          loc `shouldSatisfy` isJust
          srcLocFile (fromJust loc) `shouldBe` "src/Control/Hspl/List.hs"
          srcLocModule (fromJust loc) `shouldBe` "Control.Hspl.List"
          scope `shouldSatisfy` isNothing
#else
          loc `shouldSatisfy` isNothing
          scope `shouldBe` Just "Control.Hspl.List"
#endif

    withParams [ L.member?('a', __)
               , L.length?("foo", __)
               , L.delete?(__, 'a', __)
               , L.nth?(__, __, 'a')
               ] $ \p ->
      it "should indicate the module where the predicate is defined" $
        case astGoal p of
          PredGoal p cs -> runTest p >> forM_ cs (\(HornClause p _) -> runTest p)
          g -> failure $ "Expected PredGoal but got " ++ show g
