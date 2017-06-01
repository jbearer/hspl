{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -fdefer-type-errors #-}
#endif

module AstTest where

import Data.Data

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Tuple
#if __GLASGOW_HASKELL__ >= 800
import Test.ShouldNotTypecheck
#endif

foo = predicate "foo" ()
bar = predicate "bar" True
baz = predicate "baz" (True, ())

predNamed x = predicate x ()

data Tree a = Leaf a | Tree a (Tree a) (Tree a)
  deriving (Show, Eq, Typeable, Data)

data PseudoTree a = PLeaf a | PTree a (PseudoTree a) (PseudoTree a)
  deriving (Show, Eq, Typeable, Data)

data U = U
  deriving (Show, Eq, Typeable, Data)

data PseudoU = PU
  deriving (Show, Eq, Typeable, Data)

data Binary a = Binary a a
  deriving (Show, Eq, Typeable, Data)

data TwoChars = TwoChars Char Char
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
      toTerm (True, 'a') `shouldBe` Tup (Constant True) (Constant 'a')
      toTerm (True, 'a', ()) `shouldBe` Tup (Constant True) (Tup (Constant 'a') (Constant ()))
      toTerm ((), (), ()) `shouldBe`
        Tup (Constant ()) (
        Tup (Constant ())
                (Constant ()))
      toTerm ((), (), (), ()) `shouldBe`
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ())
                (Constant ())))
      toTerm ((), (), (), (), ()) `shouldBe`
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ())
                (Constant ()))))
      toTerm ((), (), (), (), (), ()) `shouldBe`
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ())
                (Constant ())))))
      toTerm ((), (), (), (), (), (), ()) `shouldBe`
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ()) (
        Tup (Constant ())
                (Constant ()))))))

      -- Nested tuples have the same internal represetation as flat tuples, but a different type
      toTerm (True, ('a', ())) `shouldBe` Tup (Constant True) (Tup (Constant 'a') (Constant ()))
      toTerm (True, 'a', (), 'b') `shouldBe`
        Tup (Constant True) (
        Tup (Constant 'a') (
        Tup (Constant ())
                (Constant 'b')))
      toTerm (True, ('a', ((), 'b'))) `shouldBe`
        Tup (Constant True) (
        Tup (Constant 'a') (
        Tup (Constant ())
                (Constant 'b')))
      toTerm (True, ('a', (), 'b')) `shouldBe`
        Tup (Constant True) (
        Tup (Constant 'a') (
        Tup (Constant ())
                (Constant 'b')))
    it "can be constructed from lists" $ do
      toTerm "foo" `shouldBe` List (Constant 'f') (List (Constant 'o') (List (Constant 'o') Nil))
      toTerm ("foo", [True, False]) `shouldBe`
        Tup (List (Constant 'f') (List (Constant 'o') (List (Constant 'o') Nil)))
                (List (Constant True) (List (Constant False) Nil))
    it "should provide sufficient generality to represent ADTs" $ do
      -- TODO Cannot yet support nested constructors like 'Tree', because the subterms need to be
      -- 'TermData'. This will be fixed in the next commit.
      adt Leaf True `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm True]
      adt Leaf ('a', 'b') `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm ('a', 'b')]
      adt Binary ('a', 'b') `shouldBe`
        Constructor (toConstr $ Binary 'a' 'b') [ETerm $ toTerm 'a', ETerm $ toTerm 'b']
    it "cannot be constructed from mismatched ADT constructors and arguments" $ do
#if __GLASGOW_HASKELL__ >= 800
      shouldNotTypecheck (adt TwoChars 'a')
      shouldNotTypecheck (adt TwoChars ('a', True))
      shouldNotTypecheck (adt TwoChars (True, False))
      shouldNotTypecheck (adt TwoChars ('a', 'b', 'c'))
#else
      pendingWith "ShouldNotTypecheck tests require GHC >= 8.0"
#endif
    it "should allow the representation of arithmetic expressions" $ do
      termType (Sum (toTerm (42 :: Int)) (toTerm (Var "x" :: Var Int))) `shouldBe`
        typeOf (42 :: Int)
      termType (Difference (toTerm (1.0 :: Double)) (toTerm (Var "x" :: Var Double))) `shouldBe`
        typeOf (1.0 :: Double)
      termType (Product (toTerm (42 :: Int)) (toTerm (Var "x" :: Var Int))) `shouldBe`
        typeOf (42 :: Int)
      termType (Quotient (toTerm (1.0 :: Double)) (toTerm (Var "x" :: Var Double))) `shouldBe`
        typeOf (1.0 :: Double)
      termType (IntQuotient (toTerm (42 :: Int)) (toTerm (Var "x" :: Var Int))) `shouldBe`
        typeOf (42 :: Int)
      termType (Modulus (toTerm (42 :: Int)) (toTerm (Var "x" :: Var Int))) `shouldBe`
        typeOf (42 :: Int)
    it "can be constructed from variables any type" $ do
      toTerm (Var "x" :: Var Bool) `shouldBe` Variable (Var "x" :: Var Bool)
      toTerm (Var "x" :: Var (Tree Bool)) `shouldBe` Variable (Var "x" :: Var (Tree Bool))
      toTerm (Var "x" :: Var (Bool, String)) `shouldBe` Variable (Var "x" :: Var (Bool, String))
      toTerm (Fresh 0 :: Var Bool) `shouldBe` Variable (Fresh 0 :: Var Bool)
      toTerm (Fresh 0 :: Var (Tree Bool)) `shouldBe` Variable (Fresh 0 :: Var (Tree Bool))
      toTerm (Fresh 0 :: Var (Bool, String)) `shouldBe` Variable (Fresh 0 :: Var (Bool, String))
    it "should permit embedded variables" $ do
      toTerm (True, Var "x" :: Var Bool) `shouldBe`
        Tup (Constant True) (Variable (Var "x" :: Var Bool))
      toTerm (True, (Var "x" :: Var Bool, False)) `shouldBe`
        Tup (Constant True) (Tup (Variable $ Var "x") (Constant False))
      adt Leaf (Var "x" :: Var Bool) `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm (Var "x" :: Var Bool)]
      adt Leaf ('a', Var "x" :: Var Bool) `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm ('a', Var "x" :: Var Bool)]
      adt Binary ('a', Var "x" :: Var Char) `shouldBe`
        Constructor (toConstr $ Binary 'a' 'b') [ETerm $ toTerm 'a', ETerm $ toTerm (Var "x" :: Var Char)]
    it "should have type corresponding to the enclosed value" $ do
      termType (toTerm True) `shouldBe` typeOf True
      termType (toTerm ('a', True, ())) `shouldBe` typeOf ('a', True, ())
      termType (toTerm ('a', (True, ()))) `shouldBe` typeOf ('a', (True, ()))
      termType (toTerm (Var "x" :: Var (Tree Bool))) `shouldBe` typeOf (Leaf True)
      termType (adt Leaf True) `shouldBe` typeOf (Leaf True)
    when "containing no variables" $
      it "should reify with the corresponding Haskell value" $ do
        fromTerm (toTerm ()) `shouldBe` Just ()
        fromTerm (toTerm True) `shouldBe` Just True
        fromTerm (toTerm 'a') `shouldBe` Just 'a'
        fromTerm (toTerm (42 :: Int)) `shouldBe` Just (42 :: Int)
        fromTerm (toTerm (True, 'a')) `shouldBe` Just (True, 'a')
        fromTerm (toTerm "foo") `shouldBe` Just "foo"
        -- TODO No nested trees yet
        fromTerm (adt Leaf True) `shouldBe` Just (Leaf True)
        fromTerm (Constructor (toConstr (Nothing :: Maybe Bool)) [] :: Term (Maybe Bool)) `shouldBe` Just Nothing

        -- Two tuples with the same AST can reify to different tuples depending on whether the type
        -- is flat or nested.
        fromTerm (toTerm (True, 'a', ())) `shouldBe` Just (True, 'a', ())
        fromTerm (toTerm (True, ('a', ()))) `shouldBe` Just (True, ('a', ()))
        fromTerm (toTerm (True, 'a', (), 'b')) `shouldBe` Just (True, 'a', (), 'b')
        fromTerm (toTerm (True, ('a', ((), 'b')))) `shouldBe` Just (True, ('a', ((), 'b')))
        fromTerm (toTerm (True, ('a', (), 'b'))) `shouldBe` Just (True, ('a', (), 'b'))

        -- Arithmetic expressions
        fromTerm (Sum (toTerm (41 :: Int)) (toTerm (1 :: Int))) `shouldBe` Just 42
        fromTerm (Difference (toTerm (43 :: Int)) (toTerm (1 :: Int))) `shouldBe` Just 42
        fromTerm (Product (toTerm (7 :: Int)) (toTerm (6 :: Int))) `shouldBe` Just 42
        fromTerm (Quotient (toTerm (10.5 :: Double)) (toTerm (0.25 :: Double))) `shouldBe` Just 42.0
        fromTerm (IntQuotient (toTerm (85 :: Int)) (toTerm (2 :: Int))) `shouldBe` Just 42
        fromTerm (Modulus (toTerm (85 :: Int)) (toTerm (2 :: Int))) `shouldBe` Just 1
    when "containing variables" $
      it "fromTerm should return Nothing" $ do
        fromTerm (toTerm (Var "x" :: Var ())) `shouldBe` (Nothing :: Maybe ())
        fromTerm (toTerm (True, Var "x" :: Var Bool)) `shouldBe` (Nothing :: Maybe (Bool, Bool))
        fromTerm (adt Leaf (Var "x" :: Var Char)) `shouldBe` Nothing
        -- TODO check for nested ADTs
        fromTerm (Sum (toTerm (42 :: Int)) (toTerm (Var "x" :: Var Int))) `shouldBe` Nothing
    when "type erased" $
      it "can be mapped over" $ do
        termMap show (ETerm $ toTerm "foo") `shouldBe` show (toTerm "foo")
        termEntryMap show (ETermEntry "foo") `shouldBe` show "foo"
  describe "AdtConstructor" $ do
    it "should get the representation of a unit constructor" $
      constructor U `shouldBe` toConstr U
    it "should get the representation of a curried constructor" $ do
      constructor (Leaf :: Char -> Tree Char) `shouldBe` toConstr (Leaf 'a')
      constructor TwoChars `shouldBe` toConstr (TwoChars 'a' 'b')
  describe "AdtArgument" $
    it "should convert a tuple of arguments to a type-erased term list" $ do
      getArgs (mkTuple 'a' :: Tuple Char One) `shouldBe` [ETerm $ toTerm 'a']
      getArgs (mkTuple ('a', 'b') :: Tuple (Char, Char) One) `shouldBe` [ETerm $ toTerm ('a', 'b')]
      getArgs (mkTuple ('a', 'b') :: Tuple (Char, Char) Many) `shouldBe`
        [ETerm $ toTerm 'a', ETerm $ toTerm 'b']
      getArgs (mkTuple ('a', 'b', 'c') :: Tuple (Char, Char, Char) Many) `shouldBe`
        [ETerm $ toTerm 'a', ETerm $ toTerm 'b', ETerm $ toTerm 'c']
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
      it "should compare unequal" $
        predicate "foo" True `shouldNotEqual` predicate "foo" (True, False)
  describe "Predicate goals" $ do
    it "should compare based on the predicate" $ do
      PredGoal (predicate "foo" ()) [] `shouldEqual` PredGoal (predicate "foo" ()) []
      PredGoal (predicate "foo" ()) [] `shouldNotEqual` PredGoal (predicate "bar" ()) []
      PredGoal (predicate "foo" True) [] `shouldNotEqual` PredGoal (predicate "foo" ()) []
      PredGoal (predicate "foo" True) [] `shouldNotEqual` PredGoal (predicate "foo" False) []
    it "should compare based on the alternatives" $ do
      let c1 = HornClause (predicate "c1pred" ()) []
      let c2 = HornClause (predicate "c2pred" ()) []
      PredGoal (predicate "foo" ()) [c1] `shouldEqual` PredGoal (predicate "foo" ()) [c1]
      PredGoal (predicate "foo" ()) [c1] `shouldNotEqual` PredGoal (predicate "foo" ()) [c2]
      PredGoal (predicate "foo" ()) [c1] `shouldNotEqual` PredGoal (predicate "foo" ()) [c1, c2]
  describe "CanUnify goals" $ do
    context "of the same type" $
      it "should compare according to the arguments" $ do
        CanUnify (toTerm 'a') (toTerm 'b') `shouldEqual` CanUnify (toTerm 'a') (toTerm 'b')
        CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'b') `shouldEqual`
          CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'b')
        CanUnify (toTerm 'a') (toTerm 'b') `shouldNotEqual` CanUnify (toTerm 'a') (toTerm 'a')
        CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'b') `shouldNotEqual`
          CanUnify (toTerm (Var "y" :: Var Char)) (toTerm 'b')
    context "of different types" $
      it "should compare unequal" $ do
        CanUnify (toTerm 'a') (toTerm 'b') `shouldNotEqual` CanUnify (toTerm True) (toTerm False)
        CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)) `shouldNotEqual`
          CanUnify (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))
  describe "Identical goals" $ do
    context "of the same type" $
      it "should compare according to the arguments" $ do
        Identical (toTerm 'a') (toTerm 'b') `shouldEqual` Identical (toTerm 'a') (toTerm 'b')
        Identical (toTerm (Var "x" :: Var Char)) (toTerm 'b') `shouldEqual`
          Identical (toTerm (Var "x" :: Var Char)) (toTerm 'b')
        Identical (toTerm 'a') (toTerm 'b') `shouldNotEqual` Identical (toTerm 'a') (toTerm 'a')
        Identical (toTerm (Var "x" :: Var Char)) (toTerm 'b') `shouldNotEqual`
          Identical (toTerm (Var "y" :: Var Char)) (toTerm 'b')
    context "of different types" $
      it "should compare unequal" $ do
        Identical (toTerm 'a') (toTerm 'b') `shouldNotEqual` Identical (toTerm True) (toTerm False)
        Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)) `shouldNotEqual`
          Identical (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))
  describe "Not goals" $
    it "should compare according to the inner goal" $ do
      Not (PredGoal (predicate "foo" ()) []) `shouldEqual` Not (PredGoal (predicate "foo" ()) [])
      Not (PredGoal (predicate "foo" ()) []) `shouldNotEqual` Not (PredGoal (predicate "bar" ()) [])
  describe "Equal goals" $ do
    context "of the same type" $
      it "should compare according to the arguments" $ do
        Equal (toTerm (1 :: Int)) (toTerm (2 :: Int)) `shouldEqual`
          Equal (toTerm (1 :: Int)) (toTerm (2 :: Int))
        Equal (toTerm (Var "x" :: Var Int)) (toTerm (1 :: Int)) `shouldEqual`
          Equal (toTerm (Var "x" :: Var Int)) (toTerm (1 :: Int))
        Equal (toTerm (1 :: Int)) (toTerm (2 :: Int)) `shouldNotEqual`
          Equal (toTerm (1 :: Int)) (toTerm (1 :: Int))
        Equal (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int)) `shouldNotEqual`
          Equal (toTerm (Var "y" :: Var Int)) (toTerm (2 :: Int))
    context "of different types" $
      it "should compare unequal" $ do
        Equal (toTerm (1 :: Int)) (toTerm (2 :: Int)) `shouldNotEqual`
          Equal (toTerm (1.0 :: Double)) (toTerm (2.0 :: Double))
        Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int)) `shouldNotEqual`
          Equal (toTerm (Var "x" :: Var Double)) (toTerm (Var "y" :: Var Double))
  describe "clauses" $ do
    it "should have type corresponding to the type of the positive literal" $ do
      clauseType (HornClause foo []) `shouldBe` predType foo
      clauseType (HornClause foo [PredGoal (predicate "P" ()) []]) `shouldBe` predType foo
      clauseType (HornClause foo [PredGoal (predicate "P" ()) [], PredGoal (predicate "Q" (True, 'a')) []])
        `shouldBe` predType foo
    it "should compare according to the literals" $ do
      HornClause foo [] `shouldEqual` HornClause foo []
      HornClause foo [PredGoal bar [], PredGoal baz []] `shouldEqual`
        HornClause foo [PredGoal bar [], PredGoal baz []]
      HornClause foo [] `shouldNotEqual` HornClause foo [PredGoal bar []]
      HornClause foo [PredGoal bar [], PredGoal baz []] `shouldNotEqual`
        HornClause bar [PredGoal foo [], PredGoal baz []]
      HornClause (predicate "P" ()) [] `shouldNotEqual` HornClause (predicate "P" True) []
