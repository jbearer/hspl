{-# LANGUAGE FlexibleContexts #-} -- Needed by GHC < 8.0 for HasCallStack contexts

module Util where

import Data.CallStack
import Test.Hspec
import Test.HUnit

describeModule :: String -> SpecWith a -> SpecWith a
describeModule = describe . ("in the module " ++)

when :: String -> SpecWith a -> SpecWith a
when = context . ("when " ++)

shouldEqual :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldEqual = shouldBe

shouldNotEqual :: (HasCallStack, Show a, Eq a) => a -> a -> Expectation
shouldNotEqual = shouldNotBe
