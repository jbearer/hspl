{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

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
  ) where

import Data.CallStack
import Test.Hspec hiding (shouldNotBe)
import Test.Hspec (shouldBe)
import Test.HUnit

describeModule :: String -> SpecWith a -> SpecWith a
describeModule = describe . ("in the module " ++)

when :: String -> SpecWith a -> SpecWith a
when = context . ("when " ++)

shouldEqual :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldEqual = shouldBe

shouldNotBe :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldNotBe x y
  | x == y = assertFailure $ "Expected: " ++ show x ++ "\nnot to equal: " ++ show y
  | otherwise = assertBool "" True

shouldNotEqual :: (HasCallStack, Show a, Eq a) => a -> a-> Expectation
shouldNotEqual = shouldNotBe
