{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraint
{-# LANGUAGE UndecidableInstances #-}

-- Abstraction layer on top of HSpec, plus some additional combinators. This is necessary because
-- versions of HSpec < 2.4 do not include the shouldNotBe expectation, which is used by many tests.
module Testing (
    describe
  , it
  , context
  , describeModule
  , when
  , withParams
  , shouldEqual
  , shouldBe
  , shouldNotEqual
  , shouldNotBe
  , shouldSatisfy
  , shouldNotSatisfy
  , shouldBeOneOf
  , shouldBePermutationOf
  , shouldBeSubsetOf
  , pending
  , pendingWith
  , AssertError (..)
  , shouldBeAlphaEquivalentTo
  , failure
  , success
  ) where

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate, try, ErrorCall (..))
import Control.Monad (forM_)
import Data.CallStack
import Data.List
import Test.Hspec hiding (shouldNotBe, shouldNotSatisfy)
import Test.Hspec (shouldBe)
import Test.HUnit

import Control.Hspl.Internal.Ast

success :: Expectation
success = assertBool "" True

failure :: String -> Expectation
failure = assertFailure

describeModule :: String -> SpecWith a -> SpecWith a
describeModule = describe . ("in the module " ++)

when :: String -> SpecWith a -> SpecWith a
when = context . ("when " ++)

withParams :: [a] -> (a -> SpecWith ()) -> SpecWith ()
withParams = forM_

shouldEqual :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldEqual = shouldBe

shouldNotBe :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldNotBe x y
  | x == y = failure $ "Expected: " ++ show x ++ "\nnot to equal: " ++ show y
  | otherwise = success

shouldNotEqual :: (HasCallStack, Show a, Eq a) => a -> a-> Expectation
shouldNotEqual = shouldNotBe

shouldNotSatisfy :: (HasCallStack, Show a, Eq a) => a -> (a -> Bool) -> Expectation
shouldNotSatisfy a f = a `shouldSatisfy` (not . f)

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

shouldBeOneOf :: (HasCallStack, Show a, Eq a) => a -> [a] -> Expectation
shouldBeOneOf x xs
  | x `elem` xs = success
  | otherwise = failure $ "Expected " ++ show x ++ " to be one of " ++ show xs

shouldBePermutationOf :: (HasCallStack, Show a, Eq a) => [a] -> [a] -> Expectation
shouldBePermutationOf xs ys
  | xs `isPermutationOf` ys = success
  | otherwise = failure $ "Expected: " ++ show xs ++ "\nto be a permuatation of: " ++ show ys

shouldBeSubsetOf :: (HasCallStack, Show a, Eq a) => [a] -> [a] -> Expectation
shouldBeSubsetOf xs ys
  | xs `isSubsetOf` ys = success
  | otherwise = failure $ "Expected: " ++ show xs ++ "\nto be a subset of: " ++ show ys

shouldBeAlphaEquivalentTo :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => a -> b -> Assertion
shouldBeAlphaEquivalentTo a b = toTerm a `shouldSatisfy` alphaEquivalent (toTerm b)

class AssertError a where
  assertError :: String -> a -> Assertion

instance {-# OVERLAPPABLE #-} (NFData a, Show a) => AssertError a where
  assertError expected expr = assertError expected $ evaluate $ force expr

instance {-# OVERLAPPING #-} Show a => AssertError (IO a) where
  assertError expected expr = do
    result <- try expr
    case result of
      Right r -> assertFailure $ "Expected the expression " ++ show r ++ " to raise an error:\n" ++
                                 expected
      Left (ErrorCall msg) -> msg `shouldBe` expected
