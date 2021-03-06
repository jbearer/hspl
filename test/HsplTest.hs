{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module HsplTest where

import Testing hiding (predicate)
import qualified Testing as Test
import Control.Hspl
import qualified Control.Hspl.Internal.Ast as Ast
import           Control.Hspl.Internal.Ast (Goal (..), Var (..))
import qualified Control.Hspl.Internal.Solver as Solver
import Control.Hspl.Internal.Syntax
import qualified Control.Hspl.Internal.Syntax as Syntax

import Control.Monad.Writer
import Data.CallStack
import Data.Data
import Data.List (permutations)
import Data.Maybe (isJust, isNothing, fromJust)
import GHC.Generics

import Prelude hiding (maybe, either)

data Arities = A1 Char
             | A2 Char Char
             | A3 Char Char Char
             | A4 Char Char Char Char
             | A5 Char Char Char Char Char
             | A6 Char Char Char Char Char Char
             | A7 Char Char Char Char Char Char Char
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Arities

data BoundedEnum = E1 | E2 | E3 | E4
  deriving (Show, Eq, Typeable, Data, Generic, Ord, Bounded, Enum)
instance Termable BoundedEnum

testHsplPredScope :: Ast.Predicate -> Expectation
testHsplPredScope (Ast.Predicate loc scope _ _) = do
#if MIN_VERSION_base(4,8,1)
  loc `shouldSatisfy` isJust
  srcLocFile (fromJust loc) `shouldBe` "src/Control/Hspl.hs"
  srcLocModule (fromJust loc) `shouldBe` "Control.Hspl"
  scope `shouldSatisfy` isNothing
#else
  loc `shouldSatisfy` isNothing
  scope `shouldBe` Just "Control.Hspl"
#endif

-- base-4.9.0 changed how the end column of the expression is defined
#if MIN_VERSION_base(4,9,0)
#define FOO_END_COL 22
#else
#define FOO_END_COL 16
#endif
foo :: Predicate Char
foo = predicate "foo" $ match (v"x")
#if MIN_VERSION_base(4,8,1)
fooLoc = Just srcLoc { srcLocStartLine = __LINE__ - 2
                     , srcLocStartCol = 7
                     , srcLocEndLine = __LINE__ - 4
                     , srcLocEndCol = FOO_END_COL
                     }
#else
fooLoc = Nothing
#endif
#undef FOO_END_COL

fooDefs = [Ast.HornClause (Ast.Predicate fooLoc Nothing "foo" $ toTerm (Var "x" :: Var Char)) Top]

correctFoo t = Ast.PredGoal (Ast.Predicate fooLoc Nothing "foo" (toTerm t)) fooDefs

-- base-4.9.0 changed how the end column of the expression is defined
#if MIN_VERSION_base(4,9,0)
#define BAR_END_COL 22
#else
#define BAR_END_COL 16
#endif
bar :: Predicate (Char, Char)
bar = predicate "bar" $ match (v"x", v"y")
#if MIN_VERSION_base(4,8,1)
barLoc = Just srcLoc { srcLocStartLine = __LINE__ - 2
                     , srcLocStartCol = 7
                     , srcLocEndLine = __LINE__ - 4
                     , srcLocEndCol = BAR_END_COL
                     }
#else
barLoc = Nothing
#endif
#undef BAR_END_COL

barDefs = [Ast.HornClause (Ast.Predicate barLoc Nothing "bar" $ toTerm (Var "x" :: Var Char, Var "y" :: Var Char)) Top]

correctBar t = Ast.PredGoal (Ast.Predicate barLoc Nothing "bar" (toTerm t)) barDefs

-- base-4.9.0 changed how the end column of the expression is defined
#if MIN_VERSION_base(4,9,0)
#define GENERIC_END_COL 30
#else
#define GENERIC_END_COL 20
#endif
generic :: Ast.TermEntry a => Predicate a
generic = predicate "generic" $ match (v"x")
#if MIN_VERSION_base(4,8,1)
genericLoc = Just srcLoc { srcLocStartLine = __LINE__ - 2
                         , srcLocStartCol = 11
                         , srcLocEndLine = __LINE__ - 4
                         , srcLocEndCol = GENERIC_END_COL
                         }
#else
genericLoc = Nothing
#endif
#undef GENERIC_END_COL

genericDefs :: forall a. Ast.TermEntry a => a -> [Ast.HornClause]
genericDefs _ = [Ast.HornClause (Ast.Predicate genericLoc Nothing "generic" $ toTerm (Var "x" :: Var a)) Top]

correctGeneric :: forall a. Ast.TermData a => a -> Ast.Goal
correctGeneric t = Ast.PredGoal (Ast.Predicate genericLoc Nothing "generic" (toTerm t))
                                (genericDefs (undefined :: Ast.HSPLType a))

test = describeModule "Control.Hspl" $ do
  describe "predicate application" $ do
    it "should convert a Predicate and a TermData to a Goal" $ do
      astGoal (foo? 'a') `shouldBe` correctFoo 'a'
      astGoal (foo? char "x") `shouldBe` correctFoo (char "x")
      astGoal (bar? ('a', char "x")) `shouldBe` correctBar ('a', char "x")
    it "should handle generic predicates" $ do
      astGoal (generic? 'a') `shouldBe` correctGeneric 'a'
      astGoal (generic? "a") `shouldBe` correctGeneric "a"
      astGoal (generic? (1 :: Int)) `shouldBe` correctGeneric (1::Int)
  describe "pattern matching" $ do
    let name = "dummy"
    let run = astClause $ Test.predicate name
    it "should build a clause from a pattern and a GoalWriter" $ do
      run (match (Var "x" :: Var Char) |- foo? (Var "x" :: Var Char)) `shouldBe`
        [Ast.HornClause (Test.predicate name (Var "x" :: Var Char)) (correctFoo $ char "x")]
      run (match 'a' |- foo? (Var "x" :: Var Char)) `shouldBe`
        [Ast.HornClause (Test.predicate name 'a') (correctFoo $ char "x")]
    it "should build unit clauses" $
      run (match 'a') `shouldBe` [Ast.HornClause (Test.predicate name 'a') Top]
  describe "program execution" $ do
    let human = predicate "human" $ do { match "hypatia"; match "fred" }
    let mortal = predicate "mortal" $ match (string "x") |- human? string "x"
    it "should obtain all solutions when requested" $
      getAllTheorems (runHspl $ mortal? v"x") `shouldBe` [mortal? "hypatia", mortal? "fred"]
    it "should retrieve only the first solution when requested" $
      getAllTheorems (runHspl1 $ mortal? v"x") `shouldBe` Just (mortal? "hypatia")
    it "should retrieve at most the requested number of solutions" $
      getAllTheorems (runHsplN 1 $ mortal? v"x") `shouldBe` [mortal? "hypatia"]
    it "should handle failure gracefully" $ do
      runHspl (mortal? "bob") `shouldBe` []
      runHspl1 (mortal? "bob") `shouldBe` Nothing
      runHsplN 1 (mortal? "bob") `shouldBe` []

  describe "typed variable constructors" $ do
    it "should contruct variables of various primitive types" $ do
      bool "x" `shouldBe` (Var "x" :: Var Bool)
      int "x" `shouldBe` (Var "x" :: Var Int)
      integer "x" `shouldBe` (Var "x" :: Var Integer)
      char "x" `shouldBe` (Var "x" :: Var Char)
      string "x" `shouldBe` (Var "x" :: Var String)
      unit "x" `shouldBe` (Var "x" :: Var ())
    it "should construct Maybe variables" $ do
      maybe char "x" `shouldBe` (Var "x" :: Var (Maybe Char))
      maybe int "x" `shouldBe` (Var "x" :: Var (Maybe Int))
    it "should construct Either variables" $ do
      either char bool "x" `shouldBe` (Var "x" :: Var (Either Char Bool))
      either int double "x" `shouldBe` (Var "x" :: Var (Either Int Double))
    it "should construct variables of list type" $ do
      list bool "x" `shouldBe` (Var "x" :: Var [Bool])
      list int "x" `shouldBe` (Var "x" :: Var [Int])
      list integer "x" `shouldBe` (Var "x" :: Var [Integer])
      list char "x" `shouldBe` (Var "x" :: Var String)
      list string "x" `shouldBe` (Var "x" :: Var [String])
    it "should construct variables of tuple type" $ do
      tup (int, char) "x" `shouldBe` (Var "x" :: Var (Int, Char))
      tup (int, char, maybe bool) "x" `shouldBe` (Var "x" :: Var (Int, Char, Maybe Bool))
      tup (int, char, maybe bool, unit) "x" `shouldBe` (Var "x" :: Var (Int, Char, Maybe Bool, ()))
      tup (int, char, maybe bool, unit, double) "x" `shouldBe`
        (Var "x" :: Var (Int, Char, Maybe Bool, (), Double))
      tup (int, char, maybe bool, unit, double, integer) "x" `shouldBe`
        (Var "x" :: Var (Int, Char, Maybe Bool, (), Double, Integer))
      tup (int, char, maybe bool, unit, double, integer, tup (list string, char)) "x" `shouldBe`
        (Var "x" :: Var (Int, Char, Maybe Bool, (), Double, Integer, ([String], Char)))
    it "should deduce the type of generic variables" $ do
      auto "x" `shouldBe` (Var "x" :: Var Bool)
      auto "x" `shouldBe` (Var "x" :: Var Int)
      auto "x" `shouldBe` (Var "x" :: Var Integer)
      auto "x" `shouldBe` (Var "x" :: Var Char)
      auto "x" `shouldBe` (Var "x" :: Var String)
      v"x" `shouldBe` (Var "x" :: Var Bool)
      v"x" `shouldBe` (Var "x" :: Var Int)
      v"x" `shouldBe` (Var "x" :: Var Integer)
      v"x" `shouldBe` (Var "x" :: Var Char)
      v"x" `shouldBe` (Var "x" :: Var String)

  describe "anonymous variables" $ do
    it "should be constructible with __" $ do
      __ `shouldBe` (Anon :: Var Bool)
      __ `shouldBe` (Anon :: Var Char)
    context "of a primitive type" $
      it "should be constructible with the appropriate helper" $ do
        _bool `shouldBe` (Anon :: Var Bool)
        _int `shouldBe` (Anon :: Var Int)
        _integer `shouldBe` (Anon :: Var Integer)
        _char `shouldBe` (Anon :: Var Char)
        _string `shouldBe` (Anon :: Var String)
        _unit `shouldBe` (Anon :: Var ())
    context "of a list type" $
      it "should be constructible with _list" $ do
        _list int `shouldBe` (Anon :: Var [Int])
        _list (maybe int) `shouldBe` (Anon :: Var [Maybe Int])
    context "of a tuple type" $
      it "should be constructible with _tup" $ do
        _tup (int, char) `shouldBe` (Anon :: Var (Int, Char))
        _tup (int, char, maybe bool) `shouldBe` (Anon :: Var (Int, Char, Maybe Bool))
        _tup (int, char, maybe bool, unit) `shouldBe` (Anon :: Var (Int, Char, Maybe Bool, ()))
        _tup (int, char, maybe bool, unit, double) `shouldBe`
          (Anon :: Var (Int, Char, Maybe Bool, (), Double))
        _tup (int, char, maybe bool, unit, double, integer) `shouldBe`
          (Anon :: Var (Int, Char, Maybe Bool, (), Double, Integer))
        _tup (int, char, maybe bool, unit, double, integer, tup (list string, char)) `shouldBe`
          (Anon :: Var (Int, Char, Maybe Bool, (), Double, Integer, ([String], Char)))
    context "of a Maybe type" $
      it "should be constructible with _maybe" $ do
        _maybe char `shouldBe` (Anon :: Var (Maybe Char))
        _maybe int `shouldBe` (Anon :: Var (Maybe Int))
    context "of an Either type" $
      it "should be constructible with _either" $ do
        _either char bool `shouldBe` (Anon :: Var (Either Char Bool))
        _either int double `shouldBe` (Anon :: Var (Either Int Double))


  describe "ADT term construction" $ do
    it "should work with constructors of all arities" $ do
      A1 $$ 'a' `shouldBe` Ast.adt A1 'a'
      A2 $$ ('a', 'b') `shouldBe` Ast.adt A2 ('a', 'b')
      A3 $$ ('a', 'b', 'c') `shouldBe` Ast.adt A3 ('a', 'b', 'c')
      A4 $$ ('a', 'b', 'c', 'd') `shouldBe` Ast.adt A4 ('a', 'b', 'c', 'd')
      A5 $$ ('a', 'b', 'c', 'd', 'e') `shouldBe` Ast.adt A5 ('a', 'b', 'c', 'd', 'e')
      A6 $$ ('a', 'b', 'c', 'd', 'e', 'f') `shouldBe`
        Ast.adt A6 ('a', 'b', 'c', 'd', 'e', 'f')
      A7 $$ ('a', 'b', 'c', 'd', 'e', 'f', 'g') `shouldBe`
        Ast.adt A7 ('a', 'b', 'c', 'd', 'e', 'f', 'g')
    it "should work with variable arguments" $ do
      A1 $$ char "x" `shouldBe` Ast.adt A1 (Var "x" :: Var Char)
      A2 $$ ('a', char "x") `shouldBe` Ast.adt A2 ('a', Var "x" :: Var Char)
    it "should produce terms which can be reified" $ do
      Ast.fromTerm (A3 $$ ('a', 'b', 'c')) `shouldBe` Just (A3 'a' 'b' 'c')
      Ast.fromTerm (A4 $$ ('a', 'b' ,'c', 'd')) `shouldBe` Just (A4 'a' 'b' 'c' 'd')

  describe "predicate attributes" $ do
    let p :: ClauseWriter Char ()
        p = do match(char "x") |- true
               match(char "y") |- false
               match 'z'

-- base-4.9.0 changed how the start column of let expressions is defined
#if MIN_VERSION_base(4,9,0)
#define PATTRS_START_COL 9
#else
#define PATTRS_START_COL 18
#endif
    let pAttrs = predicate'
#if MIN_VERSION_base(4,8,1)
    let pAttrsLoc = Just srcLoc { srcLocStartLine = __LINE__ - 2
                                , srcLocStartCol = PATTRS_START_COL
                                , srcLocEndLine = __LINE__ - 4
                                , srcLocEndCol = 28
                                }
#else
    let pAttrsLoc = Nothing
#endif
#undef PATTRS_START_COL

    it "should allow the creation of scoped predicates" $
      astGoal (pAttrs [Scope "scope"] "foo" p? char "z") `shouldEqual`
        Ast.PredGoal (Ast.Predicate pAttrsLoc (Just "scope") "foo" (toTerm $ char "z"))
                     (astClause (Ast.Predicate pAttrsLoc (Just "scope") "foo") p)
    withParams [(SemiDet, once), (Theorem, track)] $ \(attr, g) ->
      it "should wrap the predicate whenever it is invoked" $
          astGoal (pAttrs [attr] "foo" p? char "z") `shouldEqual`
            astGoal (g $ tell $ Ast.PredGoal (Ast.Predicate pAttrsLoc Nothing "foo" (toTerm $ char "z"))
                                             (astClause (Ast.Predicate pAttrsLoc Nothing "foo") p))
    withParams (permutations [SemiDet, Theorem, Scope "scope"]) $ \attrs ->
      it "should apply in the order: Scope, Theorem, SemiDet" $
        astGoal (pAttrs attrs "foo" p? char "z") `shouldEqual`
          astGoal (once $ track $ tell $
            Ast.PredGoal (Ast.Predicate pAttrsLoc (Just "scope") "foo" (toTerm $ char "z"))
                         (astClause (Ast.Predicate pAttrsLoc (Just "scope") "foo") p))

  describe "the cut predicate" $
    it "should create a Cut goal" $
      astGoal cut `shouldBe` Cut

  withParams [(cutFrame, CutFrame), (track, Track), (once, Once)] $ \(p, g) ->
    describe "goal-modifying predicates" $
      it "should create a nested goal" $
        astGoal (p true) `shouldBe` g (astGoal true)

  describe "the lnot predicate" $ do
    it "should fail if the inner goal succeeds" $
      getAllTheorems (runHspl $ lnot true) `shouldBe` []
    it "should succeed if the inner goal fails" $
      getAllTheorems (runHspl $ lnot false) `shouldBe` [lnot false]

  describe "The enum predicate" $ do
    it "should backtrack over all elements of a bounded enumerable type" $ do
      let us = runHspl $ enum? (v"x" :: Var BoundedEnum)
      length us `shouldBe` 4
      queryVar (head us) (v"x") `shouldBe` Unified E1
    it "should be tagged with the correct scope" $
      case (astGoal $ enum? (char "x")) of
        Ast.PredGoal p cs ->
          testHsplPredScope p >> forM_ cs (\(Ast.HornClause p _) -> testHsplPredScope p)

  describe "list term construction" $ do
    context "via cons" $ do
      it "should prepend a value to a list variable" $
        'a' .:. Var "x" `shouldBe` Ast.List (Ast.Cons (toTerm 'a') (toTerm $ Var "x"))
      it "should prepend a variable to a list" $
        char "x" .:. "foo" `shouldBe` Ast.List (Ast.Cons (toTerm $ Var "x") (Ast.List $ Ast.Cons
                                                         (toTerm 'f') (Ast.List $ Ast.Cons
                                                         (toTerm 'o') (Ast.List $ Ast.Cons
                                                         (toTerm 'o') $ Ast.List Ast.Nil))))
      it "should be right associative" $
        char "x" .:. char "y" .:. "foo" `shouldBe` char "x" .:. (char "y" .:. "foo")
      it "should prepend a variable to a list variable" $
        char "x" .:. string "xs" `shouldBe`
          Ast.List (Ast.Cons (toTerm (Var "x" :: Var Char)) (toTerm $ Var "xs"))
    context "via concatenation" $ do
      it "should append a list of variables" $
        "ab".++.[char "x", char "y"] `shouldBe`
          Ast.List (Ast.Cons (toTerm 'a') (Ast.List $ Ast.Cons
                             (toTerm 'b') (Ast.List $ Ast.Cons
                             (toTerm $ Var "x") (Ast.List $ Ast.Cons
                             (toTerm $ Var "y")
                             $ Ast.List Ast.Nil))))
      it "should prepend a list of variables" $
        [char "x", char "y"].++."ab" `shouldBe`
          Ast.List (Ast.Cons (toTerm $ Var "x") (Ast.List $ Ast.Cons
                   (toTerm $ Var "y") (Ast.List $ Ast.Cons
                   (toTerm 'a') (Ast.List $ Ast.Cons
                   (toTerm 'b')
                   $ Ast.List Ast.Nil))))
      it "should prepend a list to a variable" $
        ['a', 'b'].++.v"xs" `shouldBe`
          Ast.List (Ast.Cons (toTerm 'a') (Ast.List $ Ast.Cons
                             (toTerm 'b')
                             (toTerm $ string "xs")))
      it "should prepend a list variable" $
        string "prefix" .++. "bar" `shouldBe` Ast.List (Ast.Append (Var "prefix") (toTerm "bar"))
      it "should parse correctly with cons" $
        'a'.:."b".++."c" `shouldBe` toTerm "abc"
    context "via nil" $
      it "should create an empty list of any type" $ do
        nil `shouldBe` toTerm ([] :: [Int])
        nil `shouldBe` toTerm ([] :: [Bool])

  describe "findAll" $
    it "should generate an Alternatives Nothing goal" $
      astGoal (findAll (char "x") (v"x" .=. 'a') (v"xs")) `shouldBe`
        Alternatives Nothing (toTerm $ char "x") (CanUnify (toTerm $ Var "x") (toTerm 'a')) (toTerm $ v"xs")
  describe "findN" $
    it "should generate an Alternatives Just goal" $
      astGoal (findN 5 (char "x") (v"x" .=. 'a') (v"xs")) `shouldBe`
        Alternatives (Just 5) (toTerm $ char "x") (CanUnify (toTerm $ Var "x") (toTerm 'a')) (toTerm $ v"xs")
  describe "bagOf" $ do
    it "should bind a list to all alternatives of a variable" $ do
      let l = enumFromTo minBound maxBound :: [BoundedEnum]
      let us = runHspl $ bagOf (v"x" :: Var BoundedEnum) (enum? (v"x" :: Var BoundedEnum)) (v"xs")
      length us `shouldBe` 1
      queryVar (head  us) (v"xs") `shouldBe` Unified l
    it "should handle ununified solutions" $ do
        let us = runHspl $ bagOf (Var "x" :: Var (Maybe Char))
                                 ((Var "x" :: Var (Maybe Char)) .=. Just $$ char "y")
                                 (v"xs")
        length us `shouldBe` 1
        case queryVar (head us) (Var "xs" :: Var [Maybe Char]) of
          Partial t -> t `shouldBeAlphaEquivalentTo` [Just $$ char "y"]
          st -> failure $ "Expected Partial (Just $$ y), but got " ++ show st

        let us = runHspl $ bagOf (char "x") (char "x" .=. char "y") (v"xs")
        length us `shouldBe` 1
        case queryVar (head us) (string "xs") of
          Partial t -> t `shouldBeAlphaEquivalentTo` [char "x"]
          st -> failure $ "Expected Partial [x], but got " ++ show st
    it "should fail if the inner goal fails" $
      runHspl (bagOf (char "x") false (v"xs")) `shouldBe` []
  describe "bagOfN" $ do
    it "should bind a list to all alternatives of a variable" $ do
      let l = enumFromTo minBound maxBound :: [BoundedEnum]
      let us = runHspl $ bagOfN 42 (v"x" :: Var BoundedEnum) (enum? (v"x" :: Var BoundedEnum)) (v"xs")
      length us `shouldBe` 1
      queryVar (head  us) (v"xs") `shouldBe` Unified l
    it "should handle ununified solutions" $ do
        let us = runHspl $ bagOfN 42 (Var "x" :: Var (Maybe Char))
                                     ((Var "x" :: Var (Maybe Char)) .=. Just $$ char "y")
                                     (v"xs")
        length us `shouldBe` 1
        case queryVar (head us) (Var "xs" :: Var [Maybe Char]) of
          Partial t -> t `shouldBeAlphaEquivalentTo` [Just $$ char "y"]
          st -> failure $ "Expected Partial (Just $$ y), but got " ++ show st

        let us = runHspl $ bagOfN 42 (char "x") (char "x" .=. char "y") (v"xs")
        length us `shouldBe` 1
        case queryVar (head us) (string "xs") of
          Partial t -> t `shouldBeAlphaEquivalentTo` [char "x"]
          st -> failure $ "Expected Partial [x], but got " ++ show st
    it "should fail if the inner goal fails" $
      runHspl (bagOfN 42 (char "x") false (v"xs")) `shouldBe` []
    it "should return at most the requested number of results" $ do
      let results = runHspl $ bagOfN 2 (v"x" :: Var BoundedEnum) (enum? (v"x" :: Var BoundedEnum)) (v"xs")
      length results `shouldBe` 1
      getTheorem (head results) `shouldBe`
        bagOfN 2 (v"x") (enum? (v"x" :: Var BoundedEnum)) (toTerm [E1, E2])
      queryVar (head results) (v"xs") `shouldBe` Unified [E1, E2]

  describe "the unified predicate" $ do
    it "should create an IsUnified goal" $
      case astGoal (unified? int "x") of
        Ast.PredGoal _ [Ast.HornClause _ g] -> g `shouldBe` IsUnified (toTerm $ int "x")
    it "should be tagged with the correct scope" $
      case astGoal (unified? int "x") of
        Ast.PredGoal p cs ->
          testHsplPredScope p >> forM_ cs (\(Ast.HornClause p _) -> testHsplPredScope p)
  describe "the variable predicate" $ do
    it "should create an IsVariable goal" $
      case astGoal (variable? int "x") of
        Ast.PredGoal _ [Ast.HornClause _ g] -> g `shouldBe` IsVariable (toTerm $ int "x")
    it "should be tagged with the correct scope" $
      case astGoal (variable? int "x") of
        Ast.PredGoal p cs ->
          testHsplPredScope p >> forM_ cs (\(Ast.HornClause p _) -> testHsplPredScope p)

-- Ugly macro so that the precedence tests work
#define TEST_TR(OP, NOP, GOAL) ( \
    describe ("term relations") $ ( \
      it "should create an appropriate AST goal from TermData" $ do { \
        astGoal ('a' OP 'b') `shouldBe` GOAL (toTerm 'a') (toTerm 'b'); \
        astGoal ('a' OP char "x") `shouldBe` GOAL (toTerm 'a') (toTerm (Var "x" :: Var Char)); \
        astGoal (char "x" OP 'a') `shouldBe` GOAL (toTerm (Var "x" :: Var Char)) (toTerm 'a'); \
        astGoal (char "x" OP char "y") `shouldBe` \
          GOAL (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)); \
      }) >> ( \
      it "should have lower precedence than binary term constructors" $ do { \
        astGoal ("foo" OP 'f' .:. "oo") `shouldBe` GOAL (toTerm "foo") (toTerm "foo"); \
        astGoal ("foo" OP "f".++."oo") `shouldBe` GOAL (toTerm "foo") (toTerm "foo"); \
        astGoal ((3::Int) OP (1::Int) .+. (2::Int)) `shouldBe` \
          GOAL (toTerm (3::Int)) ((1::Int) .+. (2::Int)); \
        astGoal ((3::Int) OP (1::Int) .*. (2::Int)) `shouldBe` \
          GOAL (toTerm (3::Int)) ((1::Int) .*. (2::Int)); \
      }) \
    ) >> ( \
    describe "negated term relations" $ ( \
      it "should negate the corresponding relation" $ do {\
        ('a' NOP 'b') `shouldBe` lnot ('a' OP 'b'); \
        ('a' NOP char "x") `shouldBe` lnot ('a' OP v"x"); \
        (char "x" NOP 'a') `shouldBe` lnot (v"x" OP 'a'); \
        (char "x" NOP char "y") `shouldBe` lnot (char "x" OP char "y"); \
      }) >> ( \
      it "should have lower precedence than binary term constructors" $ do {\
        ("foo" NOP 'f' .:. "oo") `shouldBe` lnot ("foo" OP "foo"); \
        ("foo" NOP "f".++."oo") `shouldBe` lnot ("foo" OP "foo"); \
        ((3::Int) NOP (1::Int) .+. (2::Int)) `shouldBe` \
          lnot ((3::Int) OP (1::Int) .+. (2::Int)); \
        ((3::Int) NOP (1::Int) .*. (2::Int)) `shouldBe` \
          lnot ((3::Int) OP (1::Int) .*. (2::Int)); \
      }) \
    )

  TEST_TR(.=., ./=., CanUnify)
  TEST_TR(`is`, `isnt`, Identical)
  TEST_TR(.==., ./==., Equal)

  describe "the .<. predicate" $ do
    let exec = astGoal
    it "should create a LessThan goal from two terms" $
      exec ('a' .<. 'b') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) .<. (2 :: Int) .+. (3 :: Int)) `shouldBe`
        LessThan (toTerm (1 :: Int)) (Ast.Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
  describe "the .>. predicate" $ do
    let exec = astGoal
    it "should reorder the terms to create a LessThan goal" $
      exec ('b' .>. 'a') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) .>. (2 :: Int) .+. (3 :: Int)) `shouldBe`
        LessThan (Ast.Sum (toTerm (2 :: Int)) (toTerm (3 :: Int))) (toTerm (1 :: Int))
  describe "the .<=. predicate" $ do
    let exec = astGoal
    it "should succeed if the terms are equal" $ do
      let sols = runHspl $ 'a' .<=. 'a'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` ('a' .<=. 'a')
    it "should succeed if the left-hand side is less than the right-hand side" $ do
      let sols = runHspl $ 'a' .<=. 'b'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` ('a' .<=. 'b')
    it "should unify variables on the left-hand side if possible" $ do
      let sols = runHspl $ char "x" .<=. 'a'
      length sols `shouldBe` 1
      queryVar (head sols) (char "x") `shouldBe` Unified 'a'
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) .<=. (2 :: Int) .+. (3 :: Int)) `shouldBe`
        exec ((1 :: Int) .<=. ((2 :: Int) .+. (3 :: Int)))
  describe "the .>=. predicate" $ do
    let exec = astGoal
    it "should succeed if the terms are equal" $ do
      let sols = runHspl $ 'a' .>=. 'a'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` ('a' .>=. 'a')
    it "should succeed if the left-hand side is greater than the right-hand side" $ do
      let sols = runHspl $ 'b' .>=. 'a'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` ('b' .>=. 'a')
    it "should unify variables on the left-hand side if possible" $ do
      let sols = runHspl $ char "x" .>=. 'a'
      length sols `shouldBe` 1
      queryVar (head sols) (char "x") `shouldBe` Unified 'a'
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) .>=. (2 :: Int) .+. (3 :: Int)) `shouldBe`
        exec ((1 :: Int) .>=. ((2 :: Int) .+. (3 :: Int)))

  describe "the .|. predicate" $ do
    it "should create an Or goal from two goals" $
      astGoal (foo? 'a' .|. foo? 'b') `shouldBe`
        Or (astGoal $ foo? 'a') (astGoal $ foo? 'b')
    it "should permit nested expressions" $
      astGoal (foo? 'a' .|. do {foo? 'b'; foo? 'c'}) `shouldBe`
        Or (astGoal $ foo? 'a')
           (And (astGoal $ foo? 'b')
                (astGoal $ foo? 'c'))
  describe "the .&. predicate" $ do
    it "should create an And goal from two goals" $
      astGoal (true.&.false) `shouldBe` And Top Bottom
    it "should parse correctly with .|." $ do
      true.&.false.|.cut `shouldBe` (true.&.false).|.cut
      (true.&.false.|.cut) `shouldNotBe` (true.&.(false.|.cut))
  describe "the .||. predicate" $ do
    context "when the first goal succeeds" $ do
      it "should succeed once for each result" $ do
        let rs = runHspl $ (v"x".=.'a' .|. v"x".=.'b') .||. v"x".=.'c'
        length rs `shouldBe` 2
        queryVar (head rs) (v"x") `shouldBe` Unified 'a'
        queryVar (rs !! 1) (v"x") `shouldBe` Unified 'b'
      it "should not execute the second goal" $ do
        let rs = runHspl $ (true.||.cut).|.v"x".=.'a'
        length rs `shouldBe` 2
        queryVar (rs!!1) (v"x") `shouldBe` Unified 'a'
    context "when the first goal fails" $ do
      it "should succeed when the second goal succeeds" $ do
        let rs = runHspl $ false.||.(v"x".=.'a'.|.v"x".=.'b')
        length rs `shouldBe` 2
        queryVar (head rs) (v"x") `shouldBe` Unified 'a'
        queryVar (rs !! 1) (v"x") `shouldBe` Unified 'b'
      it "should fail when the second goal fails" $
        runHspl (false.||.false) `shouldBe` []

  describe "the ifel predicate" $
    it "should create an If goal" $
      astGoal (ifel true false cut) `shouldBe` If Top Bottom Cut

  describe "the true predicate" $
    it "should create a Top goal" $
      astGoal true `shouldBe` Top
  describe "the false predicate" $
    it "should create a Bottom goal" $
      astGoal false `shouldBe` Bottom

  describe "the forAll predicate" $ do
    let testSuccess c a = getAllTheorems (runHspl $ forAll c a) `shouldBe` [forAll c a]
    it "should succeed if the condition fails" $
      testSuccess false false
    it "should succeed when the condition succeeds and the action always succeeds" $ do
      testSuccess true true
      testSuccess (int "x" .=. (3::Int) .|. int "x" .=. (2::Int) .+. (1::Int)) ((3::Int) .==. v"x")
    it "should fail when any of the actions fail" $
      runHspl (forAll (enum? (v"x" :: Var BoundedEnum)) (v"x" .=. E1)) `shouldBe` []
    it "should not bind any variables" $ do
      let results = runHspl $ forAll (v"x" .=. 'a') true
      length results `shouldBe` 1
      queryVar (head results) (char "x") `shouldBe` Ununified

      let results = runHspl $ forAll true (v"x" .=. 'a')
      length results `shouldBe` 1
      queryVar (head results) (char "x") `shouldBe` Ununified

  describe "arithmetic operators" $ do
    it "should create a sum of terms" $ do
      ((3 :: Int) .+. (2 :: Int)) `shouldBe`
        Ast.Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" .+. (2 :: Int)) `shouldBe`
        Ast.Sum (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a difference of terms" $ do
      ((3 :: Int) .-. (2 :: Int)) `shouldBe`
        Ast.Difference (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" .-. (2 :: Int)) `shouldBe`
        Ast.Difference (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a product of terms" $ do
      ((3 :: Int) .*. (2 :: Int)) `shouldBe`
        Ast.Product (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" .*. (2 :: Int)) `shouldBe`
        Ast.Product (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a quotient of fractionals" $ do
      ((3 :: Double) ./. (2 :: Double)) `shouldBe`
        Ast.Quotient (toTerm (3 :: Double)) (toTerm (2 :: Double))
      (double "x" ./. (2 :: Double)) `shouldBe`
        Ast.Quotient (toTerm (Var "x" :: Var Double)) (toTerm (2 :: Double))
    it "should create a quotient of integrals" $ do
      ((3 :: Int) .\. (2 :: Int)) `shouldBe`
        Ast.IntQuotient (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" .\. (2 :: Int)) `shouldBe`
        Ast.IntQuotient (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a modular expression" $ do
      ((3 :: Int) .%. (2 :: Int)) `shouldBe`
        Ast.Modulus (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" .%. (2 :: Int)) `shouldBe`
        Ast.Modulus (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should be left-associative" $ do
      (int "x" .+. int "y" .-. int "z") `shouldBe`
        Ast.Difference (Ast.Sum (toTerm (Var "x" :: Var Int))
                                (toTerm (Var "y" :: Var Int)))
                       (toTerm (Var "z" :: Var Int))
      (int "x" .*. int "y" .\. int "z") `shouldBe`
        Ast.IntQuotient (Ast.Product (toTerm (Var "x" :: Var Int))
                                     (toTerm (Var "y" :: Var Int)))
                        (toTerm (Var "z" :: Var Int))
      (double "x" .*. double "y" ./. double "z") `shouldBe`
        Ast.Quotient (Ast.Product (toTerm (Var "x" :: Var Double))
                                  (toTerm (Var "y" :: Var Double)))
                     (toTerm (Var "z" :: Var Double))
      (int "x" .%. int "y" .%. int "z") `shouldBe`
        Ast.Modulus (Ast.Modulus (toTerm (Var "x" :: Var Int))
                                 (toTerm (Var "y" :: Var Int)))
                    (toTerm (Var "z" :: Var Int))
    it "should give multiplication and division higher precedence than addition and subtraction" $ do
      (int "x" .+. int "y" .*. int "z") `shouldBe`
        Ast.Sum (toTerm (Var "x" :: Var Int))
                (Ast.Product (toTerm (Var "y" :: Var Int))
                             (toTerm (Var "z" :: Var Int)))
      (int "x" .-. int "y" .\. int "z") `shouldBe`
        Ast.Difference (toTerm (Var "x" :: Var Int))
                       (Ast.IntQuotient (toTerm (Var "y" :: Var Int))
                                        (toTerm (Var "z" :: Var Int)))
      (double "x" .+. double "y" ./. double "z") `shouldBe`
        Ast.Sum (toTerm (Var "x" :: Var Double))
                (Ast.Quotient (toTerm(Var "y" :: Var Double))
                              (toTerm(Var "z" :: Var Double)))
    it "should give modulus the same precedence as multiplication" $ do
      (int "x" .*. int "y" .%. int "z") `shouldBe`
        Ast.Modulus (Ast.Product (toTerm (Var "x" :: Var Int))
                                 (toTerm (Var "y" :: Var Int)))
                    (toTerm (Var "z" :: Var Int))
      (int "x" .%. int "y" .*. int "z") `shouldBe`
        Ast.Product (Ast.Modulus (toTerm (Var "x" :: Var Int))
                                 (toTerm (Var "y" :: Var Int)))
                    (toTerm (Var "z" :: Var Int))

  describe "condition blocks" $ do
    it "should fail if no condition succeeds" $
      runHspl (cond $ do { false ->> true; false ->> true }) `shouldBe` []
    it "should execute the action for the first condition that succeeds" $ do
      let g = cond $ do { true ->> v"x" .=. 'a'; true ->> v"x" .=. 'b'}
      let results = runHspl g
      getAllTheorems results `shouldBe` [cond $ do { true ->> 'a' .=. 'a'; true ->> 'a' .=. 'b'}]
      queryVar (head results) (char "x") `shouldBe` Unified 'a'

      let g = cond $ do { false ->> v"x" .=. 'a'; true ->> v"x" .=. 'b'}
      let results = runHspl g
      getAllTheorems results `shouldBe` [cond $ do { false ->> 'b' .=. 'a'; true ->> 'b' .=. 'b'}]
      queryVar (head results) (char "x") `shouldBe` Unified 'b'
    it "should make bindings in the condition" $ do
      let g = cond $ v"x" .=. 'a' ->> v"y" .=. Just $$ char"x"
      let results = runHspl g
      getAllTheorems results `shouldBe` [cond $ 'a' .=. 'a' ->> Just 'a' .=. Just 'a']
      queryVar (head results) (char "x") `shouldBe` Unified 'a'
      queryVar (head results) (auto "y") `shouldBe` Unified (Just 'a')
    it "should parse branches correctly" $ do
      let g = cond $ v"x" .==. (0::Int) .+. (1::Int) ->> v"y" .==. v"x" .+. (2::Int)
      let results = runHspl g
      getAllTheorems results `shouldBe` [cond $ (1::Int) .==. (1::Int) ->> (3::Int) .==. (3::Int)]
      queryVar (head results) (int "x") `shouldBe` Unified 1
      queryVar (head results) (int "y") `shouldBe` Unified 3
