{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -fdefer-type-errors #-}
#endif

module TupleTest where

import Testing
import Control.Hspl.Internal.Tuple
#if __GLASGOW_HASKELL__ >= 800
import Test.ShouldNotTypecheck
#endif

test = describeModule "Control.Hspl.Internal.Tuple" $ do
  describe "Tupleable" $ do
    it "should convert non-tuple values to singleton tuple" $ do
      mkTuple 'a' `shouldBe` Singleton 'a'
      mkTuple True `shouldBe` Singleton True
    it "should map tuple values to themselves when the result type is a Many tuple" $ do
      mkTuple ('a', True) `shouldBe` Tuple ('a', True)
      mkTuple ('a', True, ()) `shouldBe` Tuple ('a', True, ())
      mkTuple ('a', True, (), ('a', True)) `shouldBe` Tuple ('a', True, (), ('a', True))
      mkTuple ('a', True, (), ('a', True), "foo") `shouldBe`
        Tuple ('a', True, (), ('a', True), "foo")
      mkTuple ('a', True, (), ('a', True), "foo", 'b') `shouldBe`
        Tuple ('a', True, (), ('a', True), "foo", 'b')
      mkTuple ('a', True, (), ('a', True), "foo", 'b', False) `shouldBe`
        Tuple ('a', True, (), ('a', True), "foo", 'b', False)
    it "should map tuple values to nested singleton tuples when the result type is a One tuple" $ do
      mkTuple ('a', True) `shouldBe` Singleton ('a', True)
      mkTuple ('a', True, ()) `shouldBe` Singleton ('a', True, ())
      mkTuple ('a', True, (), ('a', True)) `shouldBe` Singleton ('a', True, (), ('a', True))
      mkTuple ('a', True, (), ('a', True), "foo") `shouldBe`
        Singleton ('a', True, (), ('a', True), "foo")
      mkTuple ('a', True, (), ('a', True), "foo", 'b') `shouldBe`
        Singleton ('a', True, (), ('a', True), "foo", 'b')
      mkTuple ('a', True, (), ('a', True), "foo", 'b', False) `shouldBe`
        Singleton ('a', True, (), ('a', True), "foo", 'b', False)
    it "should not create Many tuples from tuples of the wrong type" $ do
#if __GLASGOW_HASKELL__ >= 800
      shouldNotTypecheck (mkTuple 'a' :: Tuple (Char, Char) Many)
      shouldNotTypecheck (mkTuple ('a', True) :: Tuple (Char, Char) Many)
      shouldNotTypecheck (mkTuple ('a', 'b', 'c') :: Tuple (Char, Char) Many)
      shouldNotTypecheck (mkTuple ('a', 'b') :: Tuple (Char, Char, Char) Many)
#else
      pendingWith "ShouldNotTypecheck tests require GHC >= 8.0"
#endif
  describe "TupleCons" $ do
    it "should prepend a value to a tuple" $ do
      tcons 'a' True `shouldBe` ('a', True)
      tcons 'a' (True, ()) `shouldBe` ('a', True, ())
      tcons 'a' (True, (), ('a', True)) `shouldBe` ('a', True, (), ('a', True))
      tcons 'a' (True, (), ('a', True), "foo") `shouldBe` ('a', True, (), ('a', True), "foo")
      tcons 'a' (True, (), ('a', True), "foo", 'b') `shouldBe`
        ('a', True, (), ('a', True), "foo", 'b')
      tcons 'a' (True, (), ('a', True), "foo", 'b', False) `shouldBe`
        ('a', True, (), ('a', True), "foo", 'b', False)
    it "should get the head of a tuple" $ do
      thead ('a', True) `shouldBe` 'a'
      thead ('a', True, ()) `shouldBe` 'a'
      thead ('a', True, (), ('a', True)) `shouldBe` 'a'
      thead ('a', True, (), ('a', True), "foo") `shouldBe` 'a'
      thead ('a', True, (), ('a', True), "foo", 'b') `shouldBe` 'a'
      thead ('a', True, (), ('a', True), "foo", 'b', False) `shouldBe` 'a'
    it "should get the tail of a tuple" $ do
      ttail ('a', True) `shouldBe` True
      ttail ('a', True, ()) `shouldBe` (True, ())
      ttail ('a', True, (), ('a', True)) `shouldBe` (True, (), ('a', True))
      ttail ('a', True, (), ('a', True), "foo") `shouldBe` (True, (), ('a', True), "foo")
      ttail ('a', True, (), ('a', True), "foo", 'b') `shouldBe` (True, (), ('a', True), "foo", 'b')
      ttail ('a', True, (), ('a', True), "foo", 'b', False) `shouldBe`
        (True, (), ('a', True), "foo", 'b', False)
