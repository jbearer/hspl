{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module AstTest where

import Test.Hspec
import Test.ShouldNotTypecheck

import GHC.Generics
import Data.Typeable

import Util
import Control.Hspl.Internal.Ast

foo = predicate "foo" ()
bar = predicate "bar" True
baz = predicate "baz" (True, ())

ex1 = addClause (HornClause foo [bar, baz]) emptyProgram

predNamed x = predicate x ()

data Tree a = Leaf a | Tree a (Tree a) (Tree a)
  deriving (Show, Eq, Typeable, Generic)

deriving instance (TermData a, a ~ ResolveVariables a) => TermData (Tree a)

data PseudoTree a = PLeaf a | PTree a (PseudoTree a) (PseudoTree a)
  deriving ( Show, Eq, Typeable, Generic)

deriving instance (TermData a, a ~ ResolveVariables a) => TermData (PseudoTree a)

data U = U
  deriving (Show, Eq, Typeable, Generic, TermData)

data PseudoU = PU
  deriving (Show, Eq, Typeable, Generic, TermData)

test = describeModule "Control.Hspl.Internal.Ast" $ do
  describe "variables" $ do
    it "should report the correct type" $ do
      varType (Variable "x" :: Variable Bool) `shouldBe` typeOf True
      varType (Variable "x" :: Variable (Bool, ())) `shouldBe` typeOf (True, ())
      varType (Variable "x" :: Variable (Tree Bool)) `shouldBe` typeOf (Leaf True)
    it "should compare based on name" $ do
      (Variable "x" :: Variable Bool) `shouldEqual` (Variable "x" :: Variable Bool)
      (Variable "x" :: Variable ()) `shouldNotEqual` (Variable "y" :: Variable ())
  describe "terms" $ do
    it "can be constructed from HSPL primitives" $ do
      toTerm () `shouldBe` Const ()
      toTerm True `shouldBe` Const True
      toTerm 'a' `shouldBe` Const 'a'
      toTerm (42 :: Int) `shouldBe` Const (42 :: Int)
    it "can be constructed from ADTs" $
      toTerm (Tree True (Leaf True) (Leaf False)) `shouldBe`
        (MData $ RightSum $ MCon $ Product
          (MSel $ SubTerm $ Const True)
          (Product
            (MSel $ SubTerm $ MData $ LeftSum $ MCon $ MSel $ SubTerm $ Const True)
            (MSel $ SubTerm $ MData $ LeftSum $ MCon $ MSel $ SubTerm $ Const False)))
    it "can be constructed from variables any TermData type" $ do
      toTerm (Variable "x" :: Variable Bool) `shouldBe` Var (Variable "x" :: Variable Bool)
      toTerm (Variable "x" :: Variable (Tree Bool)) `shouldBe`
        Var (Variable "x" :: Variable (Tree Bool))
      toTerm (Variable "x" :: Variable (Bool, String)) `shouldBe`
        Var (Variable "x" :: Variable (Bool, String))
    it "should permit embedded variables" $ do
      toTerm (True, Variable "x" :: Variable Bool) `shouldBe`
        (MData $ MCon $ Product (MSel $ SubTerm $ Const True) (MSel $ SubTerm $ Var (Variable "x" :: Variable Bool)))
      toTerm (True, (Variable "x" :: Variable Bool, False)) `shouldBe`
        (MData $ MCon $
          Product
            (MSel $ SubTerm $ Const True)
            (MSel $ SubTerm $ MData $ MCon $
              Product
                (MSel $ SubTerm $ Var (Variable "x" :: Variable Bool))
                (MSel $ SubTerm $ Const False)))
    it "should reject ambiguously typed variables" $ do
      -- This should work (with the type annotation)
      toTerm (Variable "x" :: Variable Bool) `shouldBe` Var (Variable "x" :: Variable Bool)
      -- But the same term without a type annotation should fail
      shouldNotTypecheck (toTerm $ Variable "x")
    when "containing no variables" $
      it "should reify with the corresponding Haskell value" $ do
        fromTerm (toTerm ()) `shouldBe` Just ()
        fromTerm (toTerm True) `shouldBe` Just True
        fromTerm (toTerm 'a') `shouldBe` Just 'a'
        fromTerm (toTerm (42 :: Int)) `shouldBe` Just (42 :: Int)
        fromTerm (toTerm (True, 'a')) `shouldBe` Just (True, 'a')
        let tree = Tree True (Leaf True) (Leaf False)
        fromTerm (toTerm tree) `shouldBe` Just tree
    when "containing variables" $
      it "fromTerm should return Nothing" $ do
        fromTerm (toTerm (Variable "x" :: Variable ())) `shouldBe` (Nothing :: Maybe ())
        fromTerm (toTerm (True, Variable "x" :: Variable Bool)) `shouldBe` (Nothing :: Maybe (Bool, Bool))
  describe "predicates" $ do
    it "should have type corresponding to the type of the argument" $ do
      predType (predicate "foo" ()) `shouldBe` typeOf (toTerm ())
      predType (predicate "foo" True) `shouldBe` typeOf (toTerm True)
      predType (predicate "foo" (True, False)) `shouldBe` typeOf (toTerm (True, False))
    context "of the same name and type" $
      it "should compare according to that type's comparison operator" $ do
        predicate "foo" True `shouldEqual` Predicate "foo" (toTerm True)
        predicate "foo" (True, ()) `shouldEqual` Predicate "foo" (toTerm (True, ()))
        predicate "foo" True `shouldNotEqual` predicate "foo" False
        predicate "foo" (True, ()) `shouldNotEqual` predicate "foo" (False, ())
    context "of the same type, but with different names" $
      it "should compare unequal" $ do
        predicate "foo" True `shouldNotEqual` predicate "bar" True
        predicate "foo" (True, ()) `shouldNotEqual` predicate "bar" (True, ())
    context "of different types" $
      it "should compare unequal" $ do
        predicate "foo" True `shouldNotEqual` predicate "foo" (True, False)
        predicate "foo" (Tree True (Leaf True) (Leaf False)) `shouldNotEqual`
          predicate "foo" (PTree True (PLeaf True) (PLeaf False))
        predicate "foo" U `shouldNotEqual` predicate "foo" PU
  describe "clauses" $ do
    it "should have type corresponding to the type of the positive literal" $ do
      clauseType (HornClause foo []) `shouldBe` predType foo
      clauseType (HornClause foo [predicate "P" ()]) `shouldBe` predType foo
      clauseType (HornClause foo [predicate "P" (), predicate "Q" (True, 'a')])
        `shouldBe` predType foo
    it "should compare according to the literals" $ do
      HornClause foo [] `shouldEqual` HornClause foo []
      HornClause foo [bar, baz] `shouldEqual` HornClause foo [bar, baz]
      HornClause foo [] `shouldNotEqual` HornClause foo [bar]
      HornClause foo [bar, baz] `shouldNotEqual` HornClause bar [foo, baz]
      HornClause (predicate "P" ()) [] `shouldNotEqual` HornClause (predicate "P" True) []
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
