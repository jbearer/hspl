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
    TestSuite
  , Expectation
  , describe
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
  , tempFile
  , tempFile2
  , predicate
  , srcLoc
  ) where

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate, try, ErrorCall (..))
import Control.Monad (forM_, unless)
import Control.Monad.IO.Class
import Data.CallStack
import Data.List
import Data.Time.Clock
import System.Directory
import System.FilePath
import Test.Hspec hiding (shouldNotBe, shouldNotSatisfy)
import Test.Hspec (shouldBe)
import Test.HUnit

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.UI

type TestSuite = SpecWith ()

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
shouldBeAlphaEquivalentTo a b
  | alphaEquivalent (toTerm a) (toTerm b) = success
  | otherwise = failure $
    "Expected: " ++ formatTerm (toTerm a) ++ "\nto be alphaEquivalent to: " ++ formatTerm (toTerm b)

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

tempFile :: MonadIO m => (String -> m a) -> m a
tempFile f = do
  tmp <- liftIO getTemporaryDirectory
  UTCTime { utctDayTime=ts } <- liftIO getCurrentTime
  let file = tmp </> "hspl-test-" ++ show ts

  exists <- liftIO $ doesFileExist file
  unless exists $ liftIO $ writeFile file ""

  result <- f file

  liftIO $ removeFile file

  return result

tempFile2 :: MonadIO m => (String -> String -> m a) -> m a
tempFile2 f = tempFile $ \f1 -> tempFile $ \f2 -> f f1 f2

-- Smart constructor for building predicates out of Haskell types. The location of the predicate is
-- in this file.
predicate :: TermData a => String -> a -> Predicate
predicate s a = Predicate (Just srcLoc) Nothing s (toTerm a)

-- Get a dummy SrcLoc object. If base >= 4.8.1, the location will correspond to the call to this
-- function. Otherwise, the location is meaningless.
srcLoc :: HasCallStack => SrcLoc
#if MIN_VERSION_base(4,8,1)
srcLoc = snd $ last callStack
#else
srcLoc = SrcLoc { srcLocPackage = "hspl-test"
                , srcLocModule = "Testing"
                , srcLocFile = "test/Testing.hs"
                , srcLocStartLine = __LINE__
                , srcLocStartCol = 0
                , srcLocEndLine = __LINE__
                , srcLocEndCol = 100
                }
#endif
