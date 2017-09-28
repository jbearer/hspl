{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module UITest where

import Testing
import Control.Hspl hiding (predicate)
import qualified Control.Hspl as Hspl
import Control.Hspl.Internal.Ast
import qualified Control.Hspl.Internal.Ast as Ast
import Control.Hspl.Internal.UI
import Control.Hspl.Internal.Syntax

import Control.Monad
import Control.Monad.Writer
import Data.Data
import Data.List
import GHC.Generics

data Pair a b = Pair a b
  deriving (Show, Eq, Typeable, Data, Generic)
instance (SubTerm a, SubTerm b) => Termable (Pair a b)

newtype IntFrac = IntFrac { toDouble :: Double }
  deriving (Num, Fractional, Real, Ord, Enum, Typeable, Data, Eq)

instance Show IntFrac where
  show = show . toDouble

instance Termable IntFrac where
  toTerm = Constant

-- This is weird and, well, bad, but it makes parameterizing the tests for numerical operators a lot
-- easier. Obviously we'll never want to depend on these operations actually behaving nicely.
instance Integral IntFrac where
  quotRem (IntFrac d1) (IntFrac d2) = quotRem (floor d1) (floor d2)
  toInteger (IntFrac d) = floor d

type BinOps a = [(a -> a -> Term (HSPLType a), String)]

binOps :: (TermData a, Num (HSPLType a), Fractional (HSPLType a), Integral (HSPLType a)) => BinOps a
binOps = [ ((.+.), ".+.")
         , ((.-.), ".-.")
         , ((.*.), ".*.")
         , ((./.), "./.")
         , ((.\.), ".\\.")
         , ((.%.), ".%.")
         ]

test :: TestSuite
test = describeModule "Control.Hspl.Internal.UI" $ do
  describe "formatType" $
    withParams [typeOf True, typeOf $ Just True, typeOf (Left True :: Either Bool Char)] $ \ty ->
      it "should show a TypeRep" $
        formatType ty `shouldBe` show ty
  describe "parensType" $ do
    withParams [typeOf $ Just True, typeOf (Left True :: Either Bool Char)] $ \ty ->
      it "should parenthesize a type with parameters" $
        parensType ty `shouldBe` ("(" ++ formatType ty ++ ")")
    it "should not parenthesize a simple type" $
      parensType (typeOf True) `shouldBe` formatType (typeOf True)

  describe "formatVariable" $ do
    it "should show the name and type of the variable" $ do
      formatVariable (Var "x" :: Var Bool) `shouldBe` ("x :: " ++ formatType (typeOf True))
      formatVariable (Var "x" :: Var (Maybe Bool)) `shouldBe`
        ("x :: " ++ formatType (typeOf $ Just True))
    it "should show Fresh variables with an underscore" $
      formatVariable (Fresh 0 :: Var Bool) `shouldBe` ("_0 :: " ++ formatType (typeOf True))
    it "should show Anon variables with two underscores" $
      formatVariable (Anon :: Var Bool) `shouldBe` ("__ :: " ++ formatType (typeOf True))
  describe "parensVariable" $
    it "should always add parentheses" $ do
      let runTest x = parensVariable x `shouldBe` ("(" ++ formatVariable x ++ ")")
      runTest (Var "x" :: Var Bool)
      runTest (Var "x" :: Var (Maybe Bool))
      runTest (Fresh 0 :: Var Bool)
      runTest (Anon :: Var Bool)

  describe "formatTerm" $ do
    let format :: TermData a => a -> String
        format = formatTerm . toTerm
    it "should show a constant" $ do
      let runTest t = formatTerm (toTerm t) `shouldBe` show t
      runTest 'a'
      runTest (1 :: Int)
      runTest (1.0 :: Double)
      runTest True

    it "should format a variable" $ do
      let runTest :: TermEntry a => Var a -> Expectation
          runTest x = formatTerm (toTerm x) `shouldBe` formatVariable x
      runTest (char "x")
      runTest (v"x" :: Var (Maybe Char))
      runTest (v"x" :: Var (Char, Bool))
      runTest (v"x" :: Var [Int])
      runTest (Fresh 0 :: Var Char)

    it "should produce a somewhat readable representation of a list" $ do
      format ([] :: [Int]) `shouldBe` "[]"
      format "foo" `shouldBe` "\"foo\""
      format [True] `shouldBe` "[True]"
      format [True, False] `shouldBe` "[True, False]"
      format [[True, False], [False, True]] `shouldBe` "[[True, False], [False, True]]"
      format (['a'] .++. [v"x"]) `shouldBe` "['a', x :: Char]"
      format ('a' .:. v"xs") `shouldBe` "['a'].++.(xs :: [Char])"

    it "should produce a somewhat readable representation of a tuple" $ do
      format (True, False) `shouldBe` "(True, False)"
      format (('a', 'b'), False) `shouldBe` "(('a', 'b'), False)"
      format (('a', True), ('b', False)) `shouldBe` "(('a', True), ('b', False))"

    it "should produce a somewhat readable representation of an adt" $ do
      format (Nothing :: Maybe Char) `shouldBe` "Nothing"
      format (Just $$ 'a') `shouldBe` "Just $$ 'a'"
      format (Pair $$ ('a', 'b')) `shouldBe` "Pair $$ ('a', 'b')"
      format (Pair $$ ('a', (True, False))) `shouldBe` "Pair $$ ('a', (True, False))"

    it "should produce a somewhat readable representation of a binary operation" $
      forM_ binOps (\(op, sop) ->
        format (IntFrac 1.0 `op` IntFrac 2.0) `shouldBe` ("1.0" ++ sop ++ "2.0")
        )

    it "should parenthesize subterms where necessary" $ do
      let subTerm = (1 :: IntFrac) .+. (2 :: IntFrac)
      let subTermNoParens = "1.0.+.2.0"
      let subTermParens = "(1.0.+.2.0)"

      -- List and tuple elements should not be parenthesized
      format [subTerm] `shouldBe` "[" ++ subTermNoParens ++ "]"
      format ('a', subTerm) `shouldBe` "('a', " ++ subTermNoParens ++ ")"

      -- ADT arguments are parenthesized only when not part of a tuple
      format (Just $$ subTerm) `shouldBe` "Just $$ " ++ subTermParens
      format (Just $$ ('a', subTerm)) `shouldBe` "Just $$ ('a', " ++ subTermNoParens ++ ")"

      -- Binary operands are always parenthesized
      forM_ binOps (\(op, sop) ->
        format (subTerm `op` subTerm) `shouldBe` (subTermParens ++ sop ++ subTermParens)
        )
  describe "parensTerm" $ do
    let shouldParens t = parensTerm (toTerm t) `shouldEqual` ("(" ++ formatTerm (toTerm t) ++ ")")
    let shouldNotParens t = parensTerm (toTerm t) `shouldEqual` formatTerm (toTerm t)
    withParams binOps $ \(op, _) ->
      it "should parenthesize binary operation expressions" $
        shouldParens ((1 :: IntFrac) `op` (2 :: IntFrac))
    it "should parenthesize adt constructors with at least one argument" $ do
        shouldParens (Just $$ 'a')
        shouldParens (Just $$ ('a', True))
    it "should not parenthesize adt constructors with no arguments" $
      shouldNotParens (Nothing :: Maybe Char)
    it "should not parenthesize constants" $
      shouldNotParens 'a'
    it "should parenthesize variables" $
      shouldParens (char "x")
    withParams [nil, toTerm ['a'], toTerm ['a', 'b'], 'a'.:.char \* "xs"] $ \l ->
      it "should not parenthesize lists" $
        shouldNotParens l
    it "should not parenthesize tuples" $ do
      shouldNotParens ('a', True)
      shouldNotParens (('a', True), ("foo", 'b'))

  describe "formatPredicate" $ do
    it "should produce a readable representation of a predicate" $
      formatPredicate (predicate "foo" 'a') `shouldBe` ("foo? " ++ formatTerm (toTerm 'a'))
    it "should parenthesize the term where necessary" $
      formatPredicate (predicate "foo" ((1 :: Int).+.(2 :: Int))) `shouldBe`
        ("foo? (" ++ formatTerm ((1 :: Int).+.(2 :: Int)) ++ ")")

  describe "formatGoal" $ do
    withParams [ PredGoal (predicate "foo" 'a') []
               , PredGoal (predicate "foo" 'a') [HornClause (predicate "foo" 'a') Top]
               ] $ \g@(PredGoal p _) ->
      it "should format the predicate of a PredGoal, ignoring the clauses" $
        formatGoal g `shouldBe` formatPredicate p
    withParams [(IsVariable, "isVariable"), (IsUnified, "isUnified")] $ \(constr, s) ->
      withParams [toTerm (1 :: Int), (1 :: Int).+.(2 :: Int)] $ \t ->
        it "should format a unary term goal" $
          formatGoal (constr t) `shouldBe` s ++ " " ++ parensTerm t
    withParams [((.=.), ".=."), (is, " `is` "), ((.==.), ".==."), ((.<.), ".<.")] $ \(op, sop) ->
      withParams [toTerm (1 :: Int), (1 :: Int) .+. (2 :: Int)] $ \t ->
        it "should format a binary term goal" $
          formatGoal (astGoal (t `op` t)) `shouldEqual`
            (parensTerm t ++ sop ++ parensTerm t)
    withParams [(lnot, "lnot"), (cutFrame, "cutFrame"), (track, "track")] $ \(op, sop) ->
      withParams (map tell [Top, Not Top]) $ \gw ->
        it "should format a unary subgoal" $
          formatGoal (astGoal $ op gw) `shouldBe`
            (sop ++ " " ++ parensGoal (astGoal gw))
    withParams [((>>), " >> "), ((.|.), ".|.")] $ \(op, sop) ->
      withParams (map tell [Top, Not Top]) $ \gw ->
        it "should format binary subgoals" $ do
          let g = astGoal gw
          formatGoal (astGoal (gw `op` gw)) `shouldBe`
            (parensGoal g ++ sop ++ parensGoal g)
    withParams [(Top, "true"), (Bottom, "false"), (Cut, "cut")] $ \(g, sg) ->
      it "should format unitary goals" $
        formatGoal g `shouldBe` sg
    withParams [toTerm $ v"x", Just $$ char "x"] $ \x ->
      withParams [Top, Not Top] $ \g ->
        withParams [toTerm $ v"xs", nil] $ \xs -> do
          it "should format an Alternatives Nothing as if it were a call to findAll" $
            formatGoal (astGoal $ findAll x (tell g) xs) `shouldBe`
              ("findAll " ++ parensTerm x ++ " " ++ parensGoal g ++ " " ++ parensTerm xs)
          it "should format an Alternatives Just as if it were a call to findN" $
            formatGoal (astGoal $ findN 42 x (tell g) xs) `shouldBe`
              ("findN 42 " ++ parensTerm x ++ " " ++ parensGoal g ++ " " ++ parensTerm xs)
  describe "parensGoal" $ do
    withParams [ PredGoal (predicate "foo" ()) []
               , CanUnify (toTerm 'a') (toTerm 'b')
               , Identical (toTerm 'a') (toTerm 'b')
               , Equal (toTerm 'a') (toTerm 'b')
               , LessThan (toTerm 'a') (toTerm 'b')
               , Not Top
               , And Top Bottom
               , Or Top Bottom
               , Alternatives Nothing (toTerm $ char "x") Top (toTerm $ char \* "xs")
               , Alternatives (Just 42) (toTerm $ char "x") Top (toTerm $ char \* "xs")
               , CutFrame Top
               ] $ \g ->
      it "should add parentheses where necessary" $
        parensGoal g `shouldBe` ("(" ++ formatGoal g ++ ")")
    withParams [Top, Bottom, Cut] $ \g ->
      it "should not add parentheses where they are not needed" $
        parensGoal g `shouldBe` formatGoal g

  describe "formatClause" $
    it "should show a ClauseWriter" $ do
      let runTest cw lns = let [c] = astClause (predicate "") cw
                           in formatClause c `shouldEqual` intercalate "\n" lns
      let foo = Hspl.predicate "foo" $ match 'a'
      runTest (match ()) ["match ()"]
      runTest ( match () |-
                  foo? 'a')
              ["match () |-"
              ,"  foo? 'a'"
              ]
      runTest ( match (Just $$ 'a') |-
                  foo? 'a')
              ["match (Just $$ 'a') |-"
              ,"  foo? 'a'"
              ]
      runTest ( match () |- do
                  foo? 'a'
                  foo? 'b')
              ["match () |- do"
              ,"  foo? 'a'"
              ,"  foo? 'b'"
              ]
