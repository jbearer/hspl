{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module AstTest where

import Test.Hspec
import Test.ShouldNotTypecheck

import GHC.Generics
import Data.Typeable
import Control.DeepSeq

import Util
import Control.Hspl.Internal.Ast

foo = predicate "foo" ()
ex1 = addClause (HornClause foo []) emptyProgram

predNamed x = predicate x ()

data Tree a = Leaf a | Tree a (Tree a) (Tree a)
  deriving (Show, Eq, Typeable, Generic, TermData)

data PseudoTree a = PLeaf a | PTree a (PseudoTree a) (PseudoTree a)
  deriving ( Show, Eq, Typeable, Generic, TermData)

data Unit = Unit
  deriving (Show, Eq, Typeable, Generic, TermData)

data PseudoUnit = PUnit
  deriving (Show, Eq, Typeable, Generic, TermData)

-- For the "shouldNotTypecheck" tests
instance NFData (Variable a) where
  rnf (Variable s) = rnf s
instance NFData TermRep where
  -- We don't actually need to deep-seq the TermRep, because the type error should arise in the
  -- Term if at all
  rnf _ = ()
instance NFData Term where
  rnf (Term t ty) = rnf t `seq` rnf ty
instance NFData Predicate where
  rnf (Predicate s t) = rnf s `seq` rnf t

test = describeModule "Control.Hspl.Internal.Ast" $ do
  describe "the unifiable class" $ do
    it "should convert HSPL primitives to terms" $ do
      term True `shouldBe` tconst True
      term 'a' `shouldBe` tconst 'a'
      term (42 :: Int) `shouldBe` tconst (42 :: Int)
      term (42 :: Integer) `shouldBe` tconst (42 :: Integer)
    it "should deconstruct ADTs" $
      term (Tree True (Leaf True) (Leaf False)) `shouldBe`
        Term
          (RightSum $
            Product (Const True) (
            Product (LeftSum $ Const True)
                    (LeftSum $ Const False)))
          (typeOf $ Leaf True)
    it "should create variables of any TermData type" $ do
      term (var "x" :: Variable Bool) `shouldBe`
        Term (Var (Variable "x" :: Variable Bool)) (typeOf True)
      term (var "x" :: Variable (Tree Bool)) `shouldBe`
        Term (Var (Variable "x" :: Variable (Tree Bool))) (typeOf $ Leaf True)
      term (var "x" :: Variable (Bool, String)) `shouldBe`
        Term (Var (Variable "x" :: Variable (Bool, String))) (typeOf (True, "foo"))
  describe "predicates" $ do
    context "of the same type" $
      it "should compare according to that type's comparison operator" $ do
        predicate "foo" True `shouldEqual` predicate "foo" True
        predicate "foo" (True, ()) `shouldEqual` predicate "foo" (True, ())
        predicate "foo" True `shouldNotEqual` predicate "foo" False
    context "of different types" $
      it "should compare unequal" $ do
        predicate "foo" True `shouldNotEqual` predicate "foo" (True, False)
        predicate "foo" (Tree True (Leaf True) (Leaf False)) `shouldNotEqual`
          predicate "foo" (PTree True (PLeaf True) (PLeaf False))
        predicate "foo" Unit `shouldNotEqual` predicate "foo" PUnit
    it "should permit embedded variables" $ do
      predicate "foo" (True, var "x" :: Variable Bool) `shouldBe`
        Predicate "foo" (Term
          (Product (Const True) (Var (Variable "x" :: Variable Bool)))
          (typeOf (True, True)))
      predicate "foo" (True, (var "x" :: Variable Bool, False)) `shouldBe`
        Predicate "foo" (Term
          (Product
            (Const True)
            (Product (Var (Variable "x" :: Variable Bool)) (Const False)))
          (typeOf (True, (True, True))))
    it "should reject ambiguously typed variables" $ do
      -- This should work (with the type annotation)
      predicate "foo" (var "x" :: Variable Bool) `shouldBe`
        Predicate "foo" (Term (Var (Variable "x" :: Variable Bool)) (typeOf True))
      -- But the same predicate without a type annotation should fail
      shouldNotTypecheck (predicate "foo" $ var "x")
  describe "the program builder" $ do
    it "should add a clause to a new predicate" $ do
      let p = foo
      let c = HornClause p []
      let m = addClause c emptyProgram
      findClauses p m `shouldBe` [c]
    it "should add additional clauses to existing predicates" $ do
      let p = foo
      let c = HornClause p [predicate "bar" ()]
      let cs = findClauses p ex1
      cs `shouldNotBe` [] -- Otherwise this test is broken
      let m = addClause c ex1
      findClauses p m `shouldBe` (c : cs)
    it "should handle clauses of the same name different types" $ do
      let p1 = predicate "pred" (True, "false")
      let p2 = predicate "pred" ()
      let m = addClauses [HornClause p1 [], HornClause p2 []] emptyProgram
      findClauses p1 m `shouldBe` [HornClause p1 []]
      findClauses p2 m `shouldBe` [HornClause p2 []]
    it "should handle clauses of the same type but different names" $ do
      let p1 = predNamed "foo"
      let p2 = predNamed "bar"
      let m = addClauses [HornClause p1 [], HornClause p2 []] emptyProgram
      findClauses p1 m `shouldBe` [HornClause p1 []]
      findClauses p2 m `shouldBe` [HornClause p2 []]
