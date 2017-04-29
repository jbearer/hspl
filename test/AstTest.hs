{-# LANGUAGE DeriveDataTypeable #-}

module AstTest where

import Data.Data

import Testing
import Control.Hspl.Internal.Ast

foo = predicate "foo" ()
bar = predicate "bar" True
baz = predicate "baz" (True, ())

ex1 = addClause (HornClause foo [bar, baz]) emptyProgram

predNamed x = predicate x ()

data Tree a = Leaf a | Tree a (Tree a) (Tree a)
  deriving (Show, Eq, Typeable, Data)

data PseudoTree a = PLeaf a | PTree a (PseudoTree a) (PseudoTree a)
  deriving (Show, Eq, Typeable, Data)

data U = U
  deriving (Show, Eq, Typeable, Data)

data PseudoU = PU
  deriving (Show, Eq, Typeable, Data)

test = describeModule "Control.Hspl.Internal.Ast" $ do
  describe "variables" $ do
    it "should report the correct type" $ do
      varType (Var "x" :: Var Bool) `shouldBe` typeOf True
      varType (Var "x" :: Var (Bool, ())) `shouldBe` typeOf (True, ())
      varType (Var "x" :: Var (Tree Bool)) `shouldBe` typeOf (Leaf True)
    it "should compare based on name" $ do
      (Var "x" :: Var Bool) `shouldEqual` (Var "x" :: Var Bool)
      (Var "x" :: Var ()) `shouldNotEqual` (Var "y" :: Var ())
  describe "terms" $ do
    it "can be constructed from HSPL primitives" $ do
      toTerm () `shouldBe` Constant ()
      toTerm True `shouldBe` Constant True
      toTerm 'a' `shouldBe` Constant 'a'
      toTerm (42 :: Int) `shouldBe` Constant (42 :: Int)
      toTerm (42 :: Integer) `shouldBe` Constant (42 :: Integer)
    it "can be constructed from tuples" $ do
      toTerm (True, 'a') `shouldBe` Product (Constant True) (Constant 'a')
      toTerm (True, 'a', ()) `shouldBe` Product (Constant True) (Product (Constant 'a') (Constant ()))
      toTerm ((), (), ()) `shouldBe`
        Product (Constant ()) (
        Product (Constant ())
                (Constant ()))
      toTerm ((), (), (), ()) `shouldBe`
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ())
                (Constant ())))
      toTerm ((), (), (), (), ()) `shouldBe`
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ())
                (Constant ()))))
      toTerm ((), (), (), (), (), ()) `shouldBe`
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ())
                (Constant ())))))
      toTerm ((), (), (), (), (), (), ()) `shouldBe`
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ()) (
        Product (Constant ())
                (Constant ()))))))

      -- Nested tuples have the same internal represetation as flat tuples, but a different type
      toTerm (True, ('a', ())) `shouldBe` Product (Constant True) (Product (Constant 'a') (Constant ()))
      toTerm (True, 'a', (), 'b') `shouldBe`
        Product (Constant True) (
        Product (Constant 'a') (
        Product (Constant ())
                (Constant 'b')))
      toTerm (True, ('a', ((), 'b'))) `shouldBe`
        Product (Constant True) (
        Product (Constant 'a') (
        Product (Constant ())
                (Constant 'b')))
      toTerm (True, ('a', (), 'b')) `shouldBe`
        Product (Constant True) (
        Product (Constant 'a') (
        Product (Constant ())
                (Constant 'b')))
    it "can be constructed from lists" $ do
      toTerm "foo" `shouldBe` List (Constant 'f') (List (Constant 'o') (List (Constant 'o') Nil))
      toTerm ("foo", [True, False]) `shouldBe`
        Product (List (Constant 'f') (List (Constant 'o') (List (Constant 'o') Nil)))
                (List (Constant True) (List (Constant False) Nil))
    it "should provide sufficient generality to represent ADTs" $ do
      termType (Constructor (\(x, y, z) -> Tree x y z)
                  (Product (Constant True)
                           (Product (Constructor Leaf $ Constant True)
                                    (Constructor Leaf $ Constant False)))) `shouldBe`
        typeOf (Leaf True)
      termType (Constructor Leaf (Constructor Leaf (Constant True))) `shouldBe`
        typeOf (Leaf (Leaf True))
    it "can be constructed from variables any type" $ do
      toTerm (Var "x" :: Var Bool) `shouldBe` Variable (Var "x" :: Var Bool)
      toTerm (Var "x" :: Var (Tree Bool)) `shouldBe` Variable (Var "x" :: Var (Tree Bool))
      toTerm (Var "x" :: Var (Bool, String)) `shouldBe` Variable (Var "x" :: Var (Bool, String))
    it "should permit embedded variables" $ do
      toTerm (True, Var "x" :: Var Bool) `shouldBe`
        Product (Constant True) (Variable (Var "x" :: Var Bool))
      toTerm (True, (Var "x" :: Var Bool, False)) `shouldBe`
        Product (Constant True) (Product (Variable $ Var "x") (Constant False))
    it "should have type corresponding to the enclosed value" $ do
      termType (toTerm True) `shouldBe` typeOf True
      termType (toTerm ('a', True, ())) `shouldBe` typeOf ('a', True, ())
      termType (toTerm ('a', (True, ()))) `shouldBe` typeOf ('a', (True, ()))
      termType (toTerm (Var "x" :: Var (Tree Bool))) `shouldBe` typeOf (Leaf True)
      termType (Constructor Leaf $ Constant True) `shouldBe` typeOf (Leaf True)
    when "containing no variables" $
      it "should reify with the corresponding Haskell value" $ do
        fromTerm (toTerm ()) `shouldBe` Just ()
        fromTerm (toTerm True) `shouldBe` Just True
        fromTerm (toTerm 'a') `shouldBe` Just 'a'
        fromTerm (toTerm (42 :: Int)) `shouldBe` Just (42 :: Int)
        fromTerm (toTerm (True, 'a')) `shouldBe` Just (True, 'a')
        fromTerm (toTerm "foo") `shouldBe` Just "foo"
        fromTerm (Constructor (\(x, y, z) -> Tree x y z)
                    (Product (Constant True)
                             (Product (Constructor Leaf $ Constant True)
                                      (Constructor Leaf $ Constant False)))) `shouldBe`
          Just (Tree True (Leaf True) (Leaf False))
        fromTerm (Constructor Leaf (Constructor Leaf (Constant True))) `shouldBe`
          Just (Leaf (Leaf True))

        -- Two tuples with the same AST can reify to different tuples depending on whether the type
        -- is flat or nested.
        fromTerm (toTerm (True, 'a', ())) `shouldBe` Just (True, 'a', ())
        fromTerm (toTerm (True, ('a', ()))) `shouldBe` Just (True, ('a', ()))
        fromTerm (toTerm (True, 'a', (), 'b')) `shouldBe` Just (True, 'a', (), 'b')
        fromTerm (toTerm (True, ('a', ((), 'b')))) `shouldBe` Just (True, ('a', ((), 'b')))
        fromTerm (toTerm (True, ('a', (), 'b'))) `shouldBe` Just (True, ('a', (), 'b'))
    when "containing variables" $
      it "fromTerm should return Nothing" $ do
        fromTerm (toTerm (Var "x" :: Var ())) `shouldBe` (Nothing :: Maybe ())
        fromTerm (toTerm (True, Var "x" :: Var Bool)) `shouldBe` (Nothing :: Maybe (Bool, Bool))
        fromTerm (Constructor (\(x, y, z) -> Tree x y z)
                    (Product (Constant True)
                             (Product (Constructor Leaf $ Constant True)
                                      (Variable $ Var "x")))) `shouldBe` Nothing
  describe "predicates" $ do
    it "should have type corresponding to the type of the argument" $ do
      predType (predicate "foo" ()) `shouldBe` termType (toTerm ())
      predType (predicate "foo" True) `shouldBe` termType (toTerm True)
      predType (predicate "foo" (True, False)) `shouldBe` termType (toTerm (True, False))
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
        -- predicate "foo" (Tree True (Leaf True) (Leaf False)) `shouldNotEqual`
        --   predicate "foo" (PTree True (PLeaf True) (PLeaf False))
        -- predicate "foo" U `shouldNotEqual` predicate "foo" PU
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
