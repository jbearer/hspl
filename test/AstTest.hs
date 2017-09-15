{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -fdefer-type-errors #-}
#endif

module AstTest where

import Control.Monad (forM_)
import Data.Data
import Data.Monoid hiding (Sum, Product)
import GHC.Generics

import Testing
import Control.DeepSeq (NFData (..))
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
  deriving (Show, Eq, Typeable, Data, Generic)
instance SubTerm a => Termable (Tree a)

data PseudoTree a = PLeaf a | PTree a (PseudoTree a) (PseudoTree a)
  deriving (Show, Eq, Typeable, Data)

data U = U
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable U

data PseudoU = PU
  deriving (Show, Eq, Typeable, Data)

data Binary a = Binary a a
  deriving (Show, Eq, Typeable, Data, Generic)
instance SubTerm a => Termable (Binary a)

data TwoChars = TwoChars Char Char
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable TwoChars

instance NFData TwoChars where
  rnf (TwoChars c1 c2) = rnf c1 `seq` rnf c2

instance NFData Constr where
  rnf c = c `seq` ()

data NoDefaultTermableInstance = NoDefault Char
  deriving (Show, Eq, Typeable, Data)
instance Termable NoDefaultTermableInstance where
  toTerm (NoDefault c) = adt NoDefault c

-- When deriving Generic instances for sum types, GHC tries to balance the sum, e.g.
-- (S1 :+: S2) :+: (S3 :+: S4), as opposed to S1 :+: (S2 :+: (S3 :+: S4)). This presents an edge
-- case for GenericAdtTerm when extracting the type-erased arguments. This 4-ary sum type should
-- force the tree-like representation and allow us to test this edge case.
data Sum4 = S1 | S2 | S3 | S4
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Sum4

-- GHC balances products the same way it does sums
data Product4 = P4 Char Char Char Char
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Product4

newtype IntFrac = IntFrac { toDouble :: Double }
  deriving (Num, Fractional, Real, Ord, Enum, Typeable, Data, Show, Eq)
instance Termable IntFrac where
  toTerm = Constant

-- This is weird and, well, bad, but it makes parameterizing the tests for numerical operators a lot
-- easier. Obviously we'll never want to depend on these operations actually behaving nicely.
instance Integral IntFrac where
  quotRem (IntFrac d1) (IntFrac d2) = quotRem (floor d1) (floor d2)
  toInteger (IntFrac d) = floor d

indeterminateConstructorError = unwords
  [ "ADT constructor could not be determined. The data constructor used in building terms must be"
  , "knowable without evaluating the term. In some cases, this means that using a function a -> b"
  , "as a constructor for a Term b is not sufficient, because the compiler does not know which"
  , "constructor will be used when the function is evaluated. Possible fix: use the data"
  , "constructor itself, rather than a function alias."
  ]

nonAdtConstructorError c = unwords
  [ "Constructor " ++ show c ++ " is not an ADT constructor. Please only use ADT constructors where"
  , "expected by HSPL."
  ]

reifyAdtTypeError i l term toType = unwords
  [ "Cannot convert " ++ term ++ " to type " ++ toType ++ " at position " ++ show i ++ " of the"
  , "argument list " ++ show l ++ "). This is most likely an HSPL bug."
  ]

reifyAdtUnderflowError c n = unwords
  [ "Not enough arguments (" ++ show n ++ ") to constructor " ++ show c ++ ". This is most likely"
  , "an HSPL bug."
  ]

reifyAdtOverflowError c expected actual = unwords
  [ "Too many arguments to constructor " ++ show c ++ ". Expected " ++ show expected ++ " but found"
  , show actual ++ ". This is most likely an HSPL bug."
  ]

test = describeModule "Control.Hspl.Internal.Ast" $ do
  describe "variables" $ do
    it "should report the correct type" $ do
      varType (Var "x" :: Var Bool) `shouldBe` typeOf True
      varType (Var "x" :: Var (Bool, ())) `shouldBe` typeOf (True, ())
      varType (Var "x" :: Var (Tree Bool)) `shouldBe` typeOf (Leaf True)
      varType (Anon :: Var Bool) `shouldBe` typeOf True
      varType (Anon :: Var (Bool, ())) `shouldBe` typeOf (True, ())
      varType (Anon :: Var (Tree Bool)) `shouldBe` typeOf (Leaf True)
      varType (Fresh 0 :: Var Bool) `shouldBe` typeOf True
      varType (Fresh 0 :: Var (Bool, ())) `shouldBe` typeOf (True, ())
      varType (Fresh 0 :: Var (Tree Bool)) `shouldBe` typeOf (Leaf True)
    it "should compare based on name" $ do
      (Var "x" :: Var Bool) `shouldEqual` (Var "x" :: Var Bool)
      (Var "x" :: Var ()) `shouldNotEqual` (Var "y" :: Var ())

      (Anon :: Var Bool) `shouldEqual` (Anon :: Var Bool)

      (Fresh 0 :: Var Bool) `shouldEqual` (Fresh 0 :: Var Bool)
      (Fresh 0 :: Var ()) `shouldNotEqual` (Fresh 1 :: Var ())

      (Var "x" :: Var Bool) `shouldNotEqual` Anon
      (Var "x" :: Var Bool) `shouldNotEqual` Fresh 0
      (Fresh 0 :: Var Bool) `shouldNotEqual` Anon
  describe "terms" $ do
    it "can be constructed from HSPL primitives" $ do
      toTerm () `shouldBe` Constant ()
      toTerm True `shouldBe` Constant True
      toTerm 'a' `shouldBe` Constant 'a'
      toTerm (42 :: Int) `shouldBe` Constant (42 :: Int)
      toTerm (42 :: Integer) `shouldBe` Constant (42 :: Integer)
    it "can be constructed from tuples" $ do
      toTerm (True, 'a') `shouldBe` Tup (Tuple2 (Constant True) (Constant 'a'))
      toTerm (True, 'a', ()) `shouldBe` Tup (TupleN (Constant True) (Tuple2 (Constant 'a') (Constant ())))
      toTerm ((), (), ()) `shouldBe`
        Tup (TupleN (Constant ()) (
             Tuple2 (Constant ())
                    (Constant ())))
      toTerm ((), (), (), ()) `shouldBe`
        Tup (TupleN (Constant ()) (
             TupleN (Constant ()) (
             Tuple2 (Constant ())
                    (Constant ()))))
      toTerm ((), (), (), (), ()) `shouldBe`
        Tup (TupleN (Constant ()) (
             TupleN (Constant ()) (
             TupleN (Constant ()) (
             Tuple2 (Constant ())
                    (Constant ())))))
      toTerm ((), (), (), (), (), ()) `shouldBe`
        Tup (TupleN (Constant ()) (
             TupleN (Constant ()) (
             TupleN (Constant ()) (
             TupleN (Constant ()) (
             Tuple2 (Constant ())
                    (Constant ()))))))
      toTerm ((), (), (), (), (), (), ()) `shouldBe`
        Tup (TupleN (Constant ()) (
             TupleN (Constant ()) (
             TupleN (Constant ()) (
             TupleN (Constant ()) (
             TupleN (Constant ()) (
             Tuple2 (Constant ())
                    (Constant ())))))))

      toTerm (True, ('a', ())) `shouldBe`
        Tup (Tuple2 (Constant True) (Tup $ Tuple2 (Constant 'a') (Constant ())))
      toTerm (True, 'a', (), 'b') `shouldBe`
        Tup (TupleN (Constant True) (
             TupleN (Constant 'a') (
             Tuple2 (Constant ())
                    (Constant 'b'))))
      toTerm (True, ('a', ((), 'b'))) `shouldBe`
        Tup (Tuple2 (Constant True) (
                    Tup (Tuple2 (Constant 'a') (
                         Tup (Tuple2 (Constant ())
                                     (Constant 'b'))))))
      toTerm (True, ('a', (), 'b')) `shouldBe`
        Tup (Tuple2 (Constant True) (
                    Tup (TupleN (Constant 'a') (
                         Tuple2 (Constant ())
                                (Constant 'b')))))
    it "can be constructed from lists" $ do
      toTerm "foo" `shouldBe` List (Cons (Constant 'f') (Cons (Constant 'o') (Cons (Constant 'o') Nil)))
      toTerm ("foo", [True, False]) `shouldBe`
        Tup (Tuple2 (List $ Cons (Constant 'f') (Cons (Constant 'o') (Cons (Constant 'o') Nil)))
                    (List $ Cons (Constant True) (Cons (Constant False) Nil)))
    it "can be constructed from ADTs" $ do
      toTerm (Tree 'a' (Leaf 'b') (Leaf 'c')) `shouldBe` adt Tree ('a', Leaf 'b', Leaf 'c')
      toTerm (Leaf True) `shouldBe` adt Leaf True
      toTerm (Leaf ('a', 'b')) `shouldBe` adt Leaf ('a', 'b')
      toTerm (Binary 'a' 'b') `shouldBe` adt Binary ('a', 'b')
      toTerm U `shouldBe` Constructor (toConstr U) []

      toTerm S1 `shouldBe` Constructor (toConstr S1) []
      toTerm S2 `shouldBe` Constructor (toConstr S2) []
      toTerm S3 `shouldBe` Constructor (toConstr S3) []
      toTerm S4 `shouldBe` Constructor (toConstr S4) []

      toTerm (P4 'a' 'b' 'c' 'd') `shouldBe` adt P4 ('a', 'b', 'c', 'd')

      -- Built-in instances
      toTerm (Just 'a') `shouldBe` adt Just 'a'
      toTerm (Nothing :: Maybe Char) `shouldBe` Constructor (toConstr (Nothing :: Maybe Char)) []
      toTerm (Left 'a' :: Either Char Bool) `shouldBe` adt Left 'a'
      toTerm (Right True :: Either Char Bool) `shouldBe` adt Right True
      toTerm (NoDefault 'a') `shouldBe` adt NoDefault 'a'
    it "cannot be constructed from mismatched ADT constructors and arguments" $ do
#if __GLASGOW_HASKELL__ >= 800
      shouldNotTypecheck (adt TwoChars 'a')
      shouldNotTypecheck (adt TwoChars ('a', True))
      shouldNotTypecheck (adt TwoChars (True, False))
      shouldNotTypecheck (adt TwoChars ('a', 'b', 'c'))
#else
      pendingWith "ShouldNotTypecheck tests require GHC >= 8.0"
#endif
    it "cannot be constructed from ADTs with variable subterms (use AdtTerm for that)" $
#if __GLASGOW_HASKELL__ >= 800
      shouldNotTypecheck (toTerm $ Just (Var "x" :: Var Char))
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
      toTerm (Anon :: Var Bool) `shouldBe` Variable (Anon :: Var Bool)
      toTerm (Anon :: Var (Tree Bool)) `shouldBe` Variable (Anon :: Var (Tree Bool))
      toTerm (Anon :: Var (Bool, String)) `shouldBe` Variable (Anon :: Var (Bool, String))
      toTerm (Fresh 0 :: Var Bool) `shouldBe` Variable (Fresh 0 :: Var Bool)
      toTerm (Fresh 0 :: Var (Tree Bool)) `shouldBe` Variable (Fresh 0 :: Var (Tree Bool))
      toTerm (Fresh 0 :: Var (Bool, String)) `shouldBe` Variable (Fresh 0 :: Var (Bool, String))
    it "should permit embedded variables" $ do
      toTerm (True, Var "x" :: Var Bool) `shouldBe`
        Tup (Tuple2 (Constant True) (Variable (Var "x" :: Var Bool)))
      toTerm (True, (Var "x" :: Var Bool, False)) `shouldBe`
        Tup (Tuple2 (Constant True) (Tup $ Tuple2 (Variable $ Var "x") (Constant False)))
      toTerm [Var "x" :: Var Char, Var "y" :: Var Char] `shouldBe`
        List (Cons (toTerm (Var "x" :: Var Char)) (
              Cons (toTerm (Var "y" :: Var Char))
              Nil))
    it "should have type corresponding to the enclosed value" $ do
      termType (toTerm True) `shouldBe` typeOf True
      termType (toTerm ('a', True, ())) `shouldBe` typeOf ('a', True, ())
      termType (toTerm ('a', (True, ()))) `shouldBe` typeOf ('a', (True, ()))
      termType (toTerm (Var "x" :: Var (Tree Bool))) `shouldBe` typeOf (Leaf True)
      termType (adt Leaf True) `shouldBe` typeOf (Leaf True)
    when "containing no variables" $ do
      it "should reify with the corresponding Haskell value" $ do
        fromTerm (toTerm ()) `shouldBe` Just ()
        fromTerm (toTerm True) `shouldBe` Just True
        fromTerm (toTerm 'a') `shouldBe` Just 'a'
        fromTerm (toTerm (42 :: Int)) `shouldBe` Just (42 :: Int)
        fromTerm (toTerm (True, 'a')) `shouldBe` Just (True, 'a')
        fromTerm (toTerm "foo") `shouldBe` Just "foo"
        fromTerm (toTerm $ Tree 'a' (Leaf 'b') (Leaf 'c')) `shouldBe`
          Just (Tree 'a' (Leaf 'b') (Leaf 'c'))
        fromTerm (toTerm $ Leaf True) `shouldBe` Just (Leaf True)
        fromTerm (toTerm (Nothing :: Maybe Bool)) `shouldBe` Just Nothing

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
      context "an ADT term" $ do
        let reify c x = reifyAdt c x :: TwoChars
        let constr = toConstr $ TwoChars 'a' 'b'
        it "should fall over when one argument is the wrong type" $ do
          let terms = [ETermEntry 'a', ETermEntry True]
          let term = "(" ++ show True ++ " :: " ++ show (typeOf True) ++ ")"
          assertError (reifyAdtTypeError 1 terms term (show $ typeOf 'a')) $ reify constr terms
        it "should fall over when given too many arguments" $ do
          let terms = [ETermEntry 'a', ETermEntry 'b', ETermEntry 'c']
          assertError (reifyAdtOverflowError constr 2 3) $ reify constr terms
        it "should fall over when given too few arguments" $ do
          let terms = [ETermEntry 'a']
          assertError (reifyAdtUnderflowError constr 1) $ reify constr terms
    when "containing variables" $
      it "fromTerm should return Nothing" $ do
        fromTerm (toTerm (Var "x" :: Var ())) `shouldBe` (Nothing :: Maybe ())
        fromTerm (toTerm (True, Var "x" :: Var Bool)) `shouldBe` (Nothing :: Maybe (Bool, Bool))
        fromTerm (adt Leaf (Var "x" :: Var Char)) `shouldBe` Nothing
        fromTerm (adt Tree ('a', Leaf 'b', Var "x" :: Var (Tree Char))) `shouldBe` Nothing
        fromTerm (adt Tree ('a', Leaf 'b', adt Leaf (Var "x" :: Var Char))) `shouldBe` Nothing
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
    it "should fall over if the constructor cannot be determined" $ do
      let constr x = if x then Leaf x else Tree x (Leaf x) (Leaf x)
      assertError indeterminateConstructorError $ constructor constr
    it "should fall over if the function is not an ADT constructor" $ do
      let f x = 42 :: Int
      assertError (nonAdtConstructorError $ toConstr (42 :: Int)) $ constructor f
  describe "AdtArgument" $
    it "should convert a tuple of arguments to a type-erased term list" $ do
      getArgs (mkTuple 'a' :: Tuple Char One) `shouldBe` [ETerm $ toTerm 'a']
      getArgs (mkTuple ('a', 'b') :: Tuple (Char, Char) One) `shouldBe` [ETerm $ toTerm ('a', 'b')]
      getArgs (mkTuple ('a', 'b') :: Tuple (Char, Char) Many) `shouldBe`
        [ETerm $ toTerm 'a', ETerm $ toTerm 'b']
      getArgs (mkTuple ('a', 'b', 'c') :: Tuple (Char, Char, Char) Many) `shouldBe`
        [ETerm $ toTerm 'a', ETerm $ toTerm 'b', ETerm $ toTerm 'c']
  describe "AdtTerm" $ do
    it "should convert a constructor and tuple of arguments to a Term" $ do
      adt Tree ('a', Leaf 'b', Leaf 'c') `shouldBe`
        Constructor (toConstr $ Tree 'a' (Leaf 'b') (Leaf 'c'))
          [ETerm $ toTerm 'a', ETerm $ toTerm (Leaf 'b'), ETerm $ toTerm (Leaf 'c')]
      adt Leaf True `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm True]
      adt Leaf ('a', 'b') `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm ('a', 'b')]
      adt Binary ('a', 'b') `shouldBe`
        Constructor (toConstr $ Binary 'a' 'b') [ETerm $ toTerm 'a', ETerm $ toTerm 'b']
    it "should allow embedded variables" $ do
      adt Leaf (Var "x" :: Var Bool) `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm (Var "x" :: Var Bool)]
      adt Leaf ('a', Var "x" :: Var Bool) `shouldBe`
        Constructor (toConstr $ Leaf True) [ETerm $ toTerm ('a', Var "x" :: Var Bool)]
      adt Binary ('a', Var "x" :: Var Char) `shouldBe`
        Constructor (toConstr $ Binary 'a' 'b')
                    [ETerm $ toTerm 'a', ETerm $ toTerm (Var "x" :: Var Char)]
      adt Tree (Var "x" :: Var Char, Leaf 'a', Leaf 'b') `shouldBe`
        Constructor (toConstr $ Tree 'a' (Leaf 'a') (Leaf 'b'))
                    [ ETerm $ toTerm (Var "x" :: Var Char)
                    , ETerm $ toTerm (Leaf 'a')
                    , ETerm $ toTerm (Leaf 'b')
                    ]
      adt Tree ('a', adt Leaf (Var "x" :: Var Char), Leaf 'b') `shouldBe`
        Constructor (toConstr $ Tree 'a' (Leaf 'b') (Leaf 'c'))
                    [ ETerm $ toTerm 'a'
                    , ETerm $ adt Leaf (Var "x" :: Var Char)
                    , ETerm $ toTerm $ Leaf 'b'
                    ]
      adt Tree ('a', Leaf 'b', Var "x" :: Var (Tree Char)) `shouldBe`
        Constructor (toConstr $ Tree 'a' (Leaf 'b') (Leaf 'c'))
                    [ ETerm $ toTerm 'a'
                    , ETerm $ toTerm $ Leaf 'b'
                    , ETerm $ toTerm (Var "x" :: Var (Tree Char))
                    ]
  describe "alpha equivalence" $ do
    context "of variables" $ do
      it "should succeed" $ do
        (Var "x" :: Var Char) `shouldBeAlphaEquivalentTo` (Var "y" :: Var Char)
        (Var "x" :: Var Char) `shouldBeAlphaEquivalentTo` (Fresh 0 :: Var Char)
        (Fresh 0 :: Var Char) `shouldBeAlphaEquivalentTo` (Var "x" :: Var Char)
      it "should work for anonymous variables" $ do
        Anon `shouldBeAlphaEquivalentTo` (Anon :: Var Char)
        Anon `shouldBeAlphaEquivalentTo` (Var "x" :: Var Char)
        (Var "x" :: Var Char) `shouldBeAlphaEquivalentTo` Anon
        (Var "x" :: Var Char, Var "y" :: Var Char) `shouldBeAlphaEquivalentTo` (Anon, Anon)
        (Anon, Anon) `shouldBeAlphaEquivalentTo` (Var "x" :: Var Char, Var "y" :: Var Char)
        (Anon, Var "x" :: Var Char) `shouldBeAlphaEquivalentTo` (Var "y" :: Var Char, Anon)
    withParams [Var "x" :: Var Char, Fresh 0, Anon] $ \x ->
      context "of a variable and a non-variable" $
        it "should fail" $ do
          toTerm x `shouldNotSatisfy` alphaEquivalent (Constant 'a')
          Constant 'a' `shouldNotSatisfy` alphaEquivalent (toTerm x)
    context "of constants" $ do
      it "should succeed when they are equal" $
        Constant 'a' `shouldBeAlphaEquivalentTo` Constant 'a'
      it "should fail when they are not" $
        Constant 'a' `shouldNotSatisfy` alphaEquivalent (Constant 'b')
    context "of tuples" $ do
      it "should succeed when the tuples are equal" $
        toTerm ('a', True) `shouldBeAlphaEquivalentTo` toTerm ('a', True)
      it "should succeed when the tuples are alpha-equivalent" $ do
        toTerm ('a', Var "x" :: Var Char) `shouldBeAlphaEquivalentTo` toTerm ('a', Var "y" :: Var Char)
        toTerm (Var "x" :: Var Char, Var "y" :: Var Char) `shouldBeAlphaEquivalentTo`
          toTerm (Var "y" :: Var Char, Var "x" :: Var Char)
        toTerm (Var "x" :: Var Char, Var "x" :: Var Char) `shouldBeAlphaEquivalentTo`
          toTerm (Var "a" :: Var Char, Var "a" :: Var Char)
      it "should fail when the tuples can be unified but are not alpha-equivalent" $ do
        toTerm (Var "x" :: Var Char, Var "y" :: Var Char) `shouldNotSatisfy`
          alphaEquivalent (toTerm (Var "a" :: Var Char, Var "a" :: Var Char))
        toTerm (Var "x" :: Var Char, Var "x" :: Var Char) `shouldNotSatisfy`
          alphaEquivalent (toTerm (Var "a" :: Var Char, Var "b" :: Var Char))
      it "should fail when the tuples are not of the same form" $
        toTerm ('a', 'b') `shouldNotSatisfy` alphaEquivalent (toTerm ('b', 'c'))
    context "of lists" $ do
      it "should succeed when the lists are equal" $
        toTerm ['a', 'b', 'c'] `shouldBeAlphaEquivalentTo` toTerm ['a', 'b', 'c']
      it "should succeed when the lists are alpha-equivalent" $ do
        toTerm ([Var "x", Var "y", Var "z"] :: [Var Char]) `shouldBeAlphaEquivalentTo`
          toTerm ([Var "a", Var "b", Var "c"] :: [Var Char])
        toTerm ([Var "x", Var "y"] :: [Var Char]) `shouldBeAlphaEquivalentTo`
          toTerm ([Var "y", Var "x"] :: [Var Char])
        toTerm ([Var "x", Var "x"] :: [Var Char]) `shouldBeAlphaEquivalentTo`
          toTerm ([Var "a", Var "a"] :: [Var Char])
      it "should fail when the lists can be unified but are not alpha-equivalent" $ do
        toTerm [Var "x" :: Var Char, Var "y" :: Var Char] `shouldNotSatisfy`
          alphaEquivalent (toTerm [Var "a" :: Var Char, Var "a" :: Var Char])
        toTerm [Var "x" :: Var Char, Var "x" :: Var Char] `shouldNotSatisfy`
          alphaEquivalent (toTerm [Var "a" :: Var Char, Var "b" :: Var Char])
      it "should fail when the lists are not of the same form" $
        toTerm ['a', 'b'] `shouldNotSatisfy` alphaEquivalent (toTerm ['b', 'c'])
    context "of adts" $ do
      it "should succeed when the terms are equal" $
        toTerm (Just 'a') `shouldBeAlphaEquivalentTo` toTerm (Just 'a')
      it "should succeed when the terms are alpha-equivalent" $
        adt Just (Var "x" :: Var Char) `shouldBeAlphaEquivalentTo` adt Just (Var "y" :: Var Char)
      it "should fail when the terms are not alpha-equivalent" $
        adt Just (Var "x" :: Var Char, Var "y" :: Var Char) `shouldNotSatisfy`
          alphaEquivalent (adt Just (Var "a" :: Var Char, Var "a" :: Var Char))
      it "should fail when the terms are not equal" $ do
        toTerm (Left 'a' :: Either Char Char) `shouldNotSatisfy`
          alphaEquivalent (toTerm (Right 'a' :: Either Char Char))
        toTerm (Leaf 'a') `shouldNotSatisfy` alphaEquivalent (toTerm $ Leaf 'b')
    context "of binary operators" $ do
      let constrs :: [Term IntFrac -> Term IntFrac -> Term IntFrac]
          constrs = [Sum, Difference, Product, Quotient, IntQuotient, Modulus]
      let term :: Double -> Term IntFrac
          term = toTerm . IntFrac
      let var :: String -> Term IntFrac
          var = toTerm . Var
      withParams constrs $ \constr -> do
        it "should succeed when the terms are equal" $
          constr (term 1) (term 2) `shouldBeAlphaEquivalentTo` constr (term 1) (term 2)
        it "should succeed when the terms are alpha-equivalent" $ do
          constr (var "x") (var "y") `shouldBeAlphaEquivalentTo` constr (var "a") (var "b")
          constr (var "x") (var "y") `shouldBeAlphaEquivalentTo` constr (var "y") (var "x")
          constr (var "x") (var "x") `shouldBeAlphaEquivalentTo` constr (var "a") (var "a")
        it "should fail when the terms can be unified but are not alpha-equivalent" $ do
          constr (var "x") (var "y") `shouldNotSatisfy` alphaEquivalent (constr (var "a") (var "a"))
          constr (var "x") (var "x") `shouldNotSatisfy` alphaEquivalent (constr (var "a") (var "b"))
        it "should fail when the terms are not of the same form" $
          constr (term 1) (term 2) `shouldNotSatisfy` alphaEquivalent (constr (term 2) (term 3))
    context "of different kinds of terms" $
      it "should fail" $
        toTerm (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int))) `shouldNotSatisfy`
          alphaEquivalent (Difference (toTerm (1 :: Int)) (toTerm (2 :: Int)))
  describe "getListTerm" $ do
    it "should return the ListTerm for a term with a List constructor" $ do
      getListTerm (List Nil :: Term [Int]) `shouldBe` Right Nil
      getListTerm (List $ Cons (toTerm 'a') Nil) `shouldBe` Right (Cons (toTerm 'a') Nil)
      getListTerm (List $ VarCons (toTerm 'a') (Var "xs")) `shouldBe`
        Right (VarCons (toTerm 'a') (Var "xs"))
    it "should return a variable when the term has a Variable constructor" $
      getListTerm (toTerm (Var "xs" :: Var [Int])) `shouldBe` Left (Var "xs")
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
    it "should compare successfully even when recursive" $ do
      let g = PredGoal (predicate "foo" 'a') [HornClause (predicate "foo" (Var "x" :: Var Char)) g]
      g `shouldEqual` g

      let g' = PredGoal (predicate "foo" 'b') [HornClause (predicate "foo" (Var "x" :: Var Char)) g']
      g' `shouldNotEqual` g

      let g'' = PredGoal (predicate "bar" 'a') [HornClause (predicate "bar" (Var "x" :: Var Char)) g'']
      g'' `shouldNotEqual` g
  withParams [(IsUnified, IsUnified), (IsVariable, IsVariable)] $ \(char, bool) ->
    describe "unary term goals" $ do
      context "of the same type" $
        it "should compare according to the arguments" $ do
          char (toTerm 'a') `shouldEqual` char (toTerm 'a')
          char (toTerm $ Var "x") `shouldEqual` char (toTerm $ Var "x")
          char (toTerm 'a') `shouldNotEqual` char (toTerm 'b')
          char (toTerm $ Var "x") `shouldNotEqual` char (toTerm $ Var "y")
      context "of different types" $
        it "should compare unequal" $ do
          char (toTerm 'a') `shouldNotEqual` bool (toTerm True)
          char (toTerm $ Var "x") `shouldNotEqual` bool (toTerm $ Var "x")
  describe "binary term goals" $ do
    let constrs :: [(Term Char -> Term Char -> Goal, Term Bool -> Term Bool -> Goal)]
        constrs = [(CanUnify, CanUnify), (Identical, Identical), (Equal, Equal), (LessThan, LessThan)]
    context "of the same type" $
      withParams constrs $ \(char, _) ->
        context "of the same type" $
          it "should compare according to the arguments" $ do
            char (toTerm 'a') (toTerm 'b') `shouldEqual` char (toTerm 'a') (toTerm 'b')
            char (toTerm (Var "x" :: Var Char)) (toTerm 'b') `shouldEqual`
              char (toTerm (Var "x" :: Var Char)) (toTerm 'b')
            char (toTerm 'a') (toTerm 'b') `shouldNotEqual` char (toTerm 'a') (toTerm 'a')
            char (toTerm (Var "x" :: Var Char)) (toTerm 'b') `shouldNotEqual`
              char (toTerm (Var "y" :: Var Char)) (toTerm 'b')
    context "of different types" $
      withParams constrs $ \(char, bool) ->
        it "should compare unequal" $ do
          char (toTerm 'a') (toTerm 'b') `shouldNotEqual` bool (toTerm True) (toTerm False)
          char (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)) `shouldNotEqual`
            bool (toTerm (Var "x" :: Var Bool)) (toTerm (Var "y" :: Var Bool))
  describe "unary outer goals" $
    withParams [Not, Once, Track] $ \constr ->
      it "should compare according to the inner goal" $ do
        constr (PredGoal (predicate "foo" ()) []) `shouldEqual`
          constr (PredGoal (predicate "foo" ()) [])
        constr (PredGoal (predicate "foo" ()) []) `shouldNotEqual`
          constr (PredGoal (predicate "bar" ()) [])
  describe "binary logic goals" $
    withParams [And, Or] $ \constr ->
      it "should compare according to the subgoals" $ do
        constr (PredGoal (predicate "foo" ()) []) (PredGoal (predicate "bar" ()) []) `shouldEqual`
          constr (PredGoal (predicate "foo" ()) []) (PredGoal (predicate "bar" ()) [])
        constr (PredGoal (predicate "foo" ()) []) (PredGoal (predicate "bar" ()) []) `shouldNotEqual`
          constr (PredGoal (predicate "foo'" ()) []) (PredGoal (predicate "bar" ()) [])
        constr (PredGoal (predicate "foo" ()) []) (PredGoal (predicate "bar" ()) []) `shouldNotEqual`
          constr (PredGoal (predicate "foo" ()) []) (PredGoal (predicate "bar'" ()) [])
  describe "unitary goals" $ do
    let ugoals = [Top, Bottom, Cut]
    withParams ugoals $ \constr -> do
      it "should equal itself" $
        constr `shouldEqual` constr
      it "should not equal any other goal" $
        constr `shouldNotEqual` And constr constr
  describe "Alternatives goals" $ do
    context "of the same type" $
      it "should compare according to the subcomponents" $ do
        let g = Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Char]))
        g `shouldEqual` g

        Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Char])) `shouldNotEqual`
          Alternatives (toTerm (Var "y" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Char]))

        Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Char])) `shouldNotEqual`
          Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'b') (toTerm 'a'))
                             (toTerm (Var "xs" :: Var [Char]))

        Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Char])) `shouldNotEqual`
          Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "ys" :: Var [Char]))
    context "of different types" $
      it "should compare unequal" $
        Alternatives (toTerm (Var "x" :: Var Char))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Char])) `shouldNotEqual`
          Alternatives (toTerm (Var "x" :: Var Bool))
                             (Equal (toTerm 'a') (toTerm 'b'))
                             (toTerm (Var "xs" :: Var [Bool]))
  describe "goals" $
    it "should form a monoid under conjunction" $ do
      mempty `shouldBe` Top
      mappend Top Bottom `shouldBe` And Top Bottom
  describe "clauses" $ do
    it "should have type corresponding to the type of the positive literal" $ do
      clauseType (HornClause foo Top) `shouldBe` predType foo
      clauseType (HornClause foo (PredGoal (predicate "P" ()) [])) `shouldBe` predType foo
      clauseType (HornClause foo (PredGoal (predicate "P" ()) [] <> PredGoal (predicate "Q" (True, 'a')) []))
        `shouldBe` predType foo
    it "should compare according to the literals" $ do
      HornClause foo Top `shouldEqual` HornClause foo Top
      HornClause foo (PredGoal bar [] <> PredGoal baz []) `shouldEqual`
        HornClause foo (PredGoal bar [] <> PredGoal baz [])
      HornClause foo Top `shouldNotEqual` HornClause foo (PredGoal bar [])
      HornClause foo (PredGoal bar [] <> PredGoal baz []) `shouldNotEqual`
        HornClause bar (PredGoal foo [] <> PredGoal baz [])
      HornClause (predicate "P" ()) Top `shouldNotEqual` HornClause (predicate "P" True) Top
