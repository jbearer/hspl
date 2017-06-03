{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraint

-- Abstraction layer on top of HSpec, plus some additional combinators. This is necessary because
-- versions of HSpec < 2.4 do not include the shouldNotBe expectation, which is used by many tests.
module Testing (
    describe
  , it
  , context
  , describeModule
  , when
  , shouldEqual
  , shouldBe
  , shouldNotEqual
  , shouldNotBe
  , shouldSatisfy
  , shouldBePermutationOf
  , shouldBeSubsetOf
  , pending
  , pendingWith
  , assertError
  ) where

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate, try, ErrorCall (..))
import Data.CallStack
import Data.List
import Test.Hspec hiding (shouldNotBe)
import Test.Hspec (shouldBe)
import Test.HUnit

success :: Expectation
success = assertBool "" True

failure :: String -> Expectation
failure = assertFailure

describeModule :: String -> SpecWith a -> SpecWith a
describeModule = describe . ("in the module " ++)

when :: String -> SpecWith a -> SpecWith a
when = context . ("when " ++)

shouldEqual :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldEqual = shouldBe

shouldNotBe :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldNotBe x y
  | x == y = failure $ "Expected: " ++ show x ++ "\nnot to equal: " ++ show y
  | otherwise = success

shouldNotEqual :: (HasCallStack, Show a, Eq a) => a -> a-> Expectation
shouldNotEqual = shouldNotBe

deleteFirst :: Eq a => a -> [a] -> [a]
deleteFirst _ [] = []
deleteFirst x (y:ys)
  | x == y = ys
  | otherwise = y : deleteFirst x ys

isPermutationOf :: Eq a => [a] -> [a] -> Bool
isPermutationOf [] [] = True
isPermutationOf (x:xs) ys
  | x `elem` ys = isPermutationOf xs (deleteFirst x ys)
  | otherwise = False

isSubsetOf :: Eq a => [a] -> [a] -> Bool
isSubsetOf [] _ = True
isSubsetOf _ [] = False
isSubsetOf (x:xs) ys
  | x `elem` ys = isSubsetOf xs (deleteFirst x ys)
  | otherwise = False

shouldBePermutationOf :: (HasCallStack, Show a, Eq a) => [a] -> [a] -> Expectation
shouldBePermutationOf xs ys
  | xs `isPermutationOf` ys = success
  | otherwise = failure $ "Expected: " ++ show xs ++ "\nto be a permuatation of: " ++ show ys

shouldBeSubsetOf :: (HasCallStack, Show a, Eq a) => [a] -> [a] -> Expectation
shouldBeSubsetOf xs ys
  | xs `isSubsetOf` ys = success
  | otherwise = failure $ "Expected: " ++ show xs ++ "\nto be a subset of: " ++ show ys

assertError :: (NFData a, Show a) => String -> (() ~ () => a) -> Assertion
assertError expected expr = do
  result <- try (evaluate $ force expr)
  case result of
    Right r -> assertFailure $ "Expected the expression " ++ show r ++ " to raise an error:\n" ++
                               expected
    Left (ErrorCall msg) -> msg `shouldBe` expected
