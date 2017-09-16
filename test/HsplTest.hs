{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HsplTest where

import Testing
import Control.Hspl
import qualified Control.Hspl.Internal.Ast as Ast
import           Control.Hspl.Internal.Ast (Goal (..), Var (..))
import qualified Control.Hspl.Internal.Solver as Solver

import Control.Monad.Writer
import Data.Data
import Data.List (permutations)
import GHC.Generics

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

foo :: Predicate Char
foo = predicate "foo" $ match (v"x")

fooDefs = [Ast.HornClause (Ast.predicate "foo" (Var "x" :: Var Char)) Top]

bar :: Predicate (Char, Char)
bar = predicate "bar" $ match (v"x", v"y")

barDefs = [Ast.HornClause (Ast.predicate "bar" (Var "x" :: Var Char, Var "y" :: Var Char)) Top]

generic :: Ast.TermEntry a => Predicate a
generic = predicate "generic" $ match (v"x")

genericDefs :: forall a. Ast.TermEntry a => a -> [Ast.HornClause]
genericDefs _ = [Ast.HornClause (Ast.predicate "generic" (Var "x" :: Var a)) Top]

test = describeModule "Control.Hspl" $ do
  describe "predicate application" $ do
    let exec = execGoalWriter
    it "should convert a Predicate and a TermData to a Goal" $ do
      exec (foo? 'a') `shouldBe` Ast.PredGoal (Ast.predicate "foo" 'a') fooDefs
      exec (foo? (Var "x" :: Var Char)) `shouldBe`
        Ast.PredGoal (Ast.predicate "foo" (Var "x" :: Var Char)) fooDefs
      exec (bar? ('a', Var "x" :: Var Char)) `shouldBe`
        Ast.PredGoal (Ast.predicate "bar" ('a', Var "x" :: Var Char)) barDefs
    it "should handle generic predicates" $ do
      exec (generic? 'a') `shouldBe` Ast.PredGoal (Ast.predicate "generic" 'a') (genericDefs 'a')
      exec (generic? "a") `shouldBe` Ast.PredGoal (Ast.predicate "generic" "a") (genericDefs "a")
      exec (generic? (1 :: Int)) `shouldBe`
        Ast.PredGoal (Ast.predicate "generic" (1 :: Int)) (genericDefs (1 :: Int))
  describe "pattern matching" $ do
    let name = "dummy"
    let run w = map ($name) $ execClauseWriter w
    it "should build a clause from a pattern and a GoalWriter" $ do
      run (match (Var "x" :: Var Char) |- foo? (Var "x" :: Var Char)) `shouldBe`
        [Ast.HornClause (Ast.predicate name (Var "x" :: Var Char))
                        (Ast.PredGoal (Ast.predicate "foo" (Var "x" :: Var Char)) fooDefs)]
      run (match 'a' |- foo? (Var "x" :: Var Char)) `shouldBe`
        [Ast.HornClause (Ast.predicate name 'a')
                        (Ast.PredGoal (Ast.predicate "foo" (Var "x" :: Var Char)) fooDefs)]
    it "should build unit clauses" $
      run (match 'a') `shouldBe` [Ast.HornClause (Ast.predicate name 'a') Top]
  describe "program execution" $ do
    let human = predicate "human" $ do { match "hypatia"; match "fred" }
    let humanDefs = [ Ast.HornClause (Ast.predicate "human" "hypatia") Top
                    , Ast.HornClause (Ast.predicate "human" "fred") Top
                    ]
    let mortal = predicate "mortal" $ match (string "x") |- human? string "x"
    let mortalDefs = [Ast.HornClause (Ast.predicate "mortal" (Var "x" :: Var String))
                                     (Ast.PredGoal (Ast.predicate "human" (Var "x" :: Var String)) humanDefs)]
    it "should obtain all solutions when requested" $
      runHspl (mortal? v"x") `shouldBe`
        Solver.runHspl
          (Ast.PredGoal (Ast.predicate "mortal" (Var "x" :: Var String)) mortalDefs)
    it "should retrieve only the first solution when requested" $
      runHspl1 (mortal? v"x") `shouldBe`
        Just (head $ Solver.runHsplN 1
          (Ast.PredGoal (Ast.predicate "mortal" (Var "x" :: Var String)) mortalDefs))
    it "should retrieve at most the requested number of solutions" $
      runHsplN 1 (mortal? v"x") `shouldBe`
        Solver.runHsplN 1
          (Ast.PredGoal (Ast.predicate "mortal" (Var "x" :: Var String)) mortalDefs)
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
    it "should construct variables of list type" $ do
      bool \* "x" `shouldBe` (Var "x" :: Var [Bool])
      int \* "x" `shouldBe` (Var "x" :: Var [Int])
      integer \* "x" `shouldBe` (Var "x" :: Var [Integer])
      char \* "x" `shouldBe` (Var "x" :: Var String)
      string \* "x" `shouldBe` (Var "x" :: Var [String])
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

  describe "anonymous variables" $
    it "should be constructible with __" $ do
      __ `shouldBe` (Anon :: Var Bool)
      __ `shouldBe` (Anon :: Var Char)

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
    withParams [(SemiDet, Once), (Theorem, Track)] $ \(attr, g) ->
      it "should wrap the predicate in once whenever it is invoked" $
          execGoalWriter (predicate' [attr] "foo" p? char "z") `shouldEqual`
            g (execGoalWriter $ predicate "foo" p? char "z")
    withParams (permutations [SemiDet, Theorem]) $ \attrs ->
      it "should apply in the order: Theorem, SemiDet" $
        execGoalWriter (predicate' attrs "foo" p? char "z") `shouldEqual`
          Once (Track $ execGoalWriter $ predicate "foo" p? char "z")

  describe "the cut predicate" $
    it "should create a Cut goal" $
      execGoalWriter cut `shouldBe` Cut

  withParams [(lnot, Not), (once, Once), (track, Track)] $ \(p, g) ->
    describe "goal-modifying predicates" $
      it "should create a nested goal" $
        execGoalWriter (p true) `shouldBe` g (execGoalWriter true)

  describe "The enum predicate" $
    it "should backtrack over all elements of a bounded enumerable type" $ do
      let us = runHspl $ enum? (v"x" :: Var BoundedEnum)
      length us `shouldBe` 4
      queryVar (head us) (v"x") `shouldBe` Unified E1

  describe "list term construction" $ do
    context "via cons" $ do
      it "should prepend a value to a list variable" $
        'a' <:> Var "x" `shouldBe` Ast.List (Ast.VarCons (toTerm 'a') (Var "x"))
      it "should prepend a variable to a list" $
        char "x" <:> "foo" `shouldBe` Ast.List (Ast.Cons (toTerm $ Var "x") (Ast.Cons
                                                         (toTerm 'f') (Ast.Cons
                                                         (toTerm 'o') (Ast.Cons
                                                         (toTerm 'o') Ast.Nil))))
      it "should be right associative" $
        char "x" <:> char "y" <:> "foo" `shouldBe` char "x" <:> (char "y" <:> "foo")
      it "should prepend a variable to a list variable" $
        char "x" <:> char \* "xs" `shouldBe`
          Ast.List (Ast.VarCons (toTerm (Var "x" :: Var Char)) (Var "xs"))
    context "via concatenation" $ do
      it "should append a list of variables" $
        "ab" <++> [char "x", char "y"] `shouldBe`
          Ast.List (Ast.Cons (toTerm 'a') (Ast.Cons
                             (toTerm 'b') (Ast.Cons
                             (toTerm $ Var "x") (Ast.Cons
                             (toTerm $ Var "y")
                             Ast.Nil))))
      it "should prepend a list of variables" $
        [char "x", char "y"] <++> "ab" `shouldBe`
          Ast.List (Ast.Cons (toTerm $ Var "x") (Ast.Cons
                   (toTerm $ Var "y") (Ast.Cons
                   (toTerm 'a') (Ast.Cons
                   (toTerm 'b')
                   Ast.Nil))))
      it "should prepend a list to a variable" $
        ['a', 'b'] <++> v"xs" `shouldBe`
          Ast.List (Ast.Cons (toTerm 'a') (Ast.VarCons
                             (toTerm 'b')
                             (char \* "xs")))
    context "via nil" $
      it "should create an empty list of any type" $ do
        nil `shouldBe` toTerm ([] :: [Int])
        nil `shouldBe` toTerm ([] :: [Bool])

  describe "findAll" $
    it "should generate an Alternatives goal" $
      execGoalWriter (findAll (char "x") (v"x" |=| 'a') (v"xs")) `shouldBe`
        Alternatives (toTerm $ char "x") (CanUnify (toTerm $ Var "x") (toTerm 'a')) (toTerm $ v"xs")
  describe "bagOf" $ do
    it "should bind a list to all alternatives of a variable" $ do
      let l = enumFromTo minBound maxBound :: [BoundedEnum]
      let us = runHspl $ bagOf (v"x" :: Var BoundedEnum) (enum? (v"x" :: Var BoundedEnum)) (v"xs")
      length us `shouldBe` 1
      queryVar (head  us) (v"xs") `shouldBe` Unified l
    it "should handle ununified solutions" $ do
        let us = runHspl $ bagOf (Var "x" :: Var (Maybe Char))
                                 ((Var "x" :: Var (Maybe Char)) |=| Just $$ char "y")
                                 (v"xs")
        length us `shouldBe` 1
        case queryVar (head us) (Var "xs" :: Var [Maybe Char]) of
          Partial t -> t `shouldBeAlphaEquivalentTo` [Just $$ char "y"]
          st -> failure $ "Expected Partial (Just $$ y), but got " ++ show st

        let us = runHspl $ bagOf (char "x") (char "x" |=| char "y") (v"xs")
        length us `shouldBe` 1
        case queryVar (head us) (char \* "xs") of
          Partial t -> t `shouldBeAlphaEquivalentTo` [char "x"]
          st -> failure $ "Expected Partial [x], but got " ++ show st
    it "should fail if the inner goal fails" $
      runHspl (bagOf (char "x") false (v"xs")) `shouldBe` []

  describe "the unified predicate" $
    it "should create an IsUnified goal" $
      execGoalWriter (unified? int "x") `shouldBe`
        PredGoal (Ast.predicate "unified" (int "x"))
                 [Ast.HornClause (Ast.predicate "unified" (int "x")) (IsUnified $ toTerm $ int "x")]
  describe "the variable predicate" $
    it "should create an IsVariable goal" $
      execGoalWriter (variable? int "x") `shouldBe`
        PredGoal (Ast.predicate "variable" (int "x"))
                 [Ast.HornClause (Ast.predicate "variable" (int "x")) (IsVariable $ toTerm $ int "x")]

  describe "the |=| predicate" $ do
    let exec = execGoalWriter
    it "should create a CanUnify goal from TermData" $ do
      exec ('a' |=| 'b') `shouldBe` CanUnify (toTerm 'a') (toTerm 'b')
      exec ('a' |=| char "x") `shouldBe` CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char))
      exec (char "x" |=| 'a') `shouldBe` CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'a')
      exec (char "x" |=| char "y") `shouldBe`
        CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))
  describe "the |\\=| predicate" $ do
    let exec = execGoalWriter
    it "should create a (Not . CanUnify) goal from TermData" $ do
      exec ('a' |\=| 'b') `shouldBe` Not (CanUnify (toTerm 'a') (toTerm 'b'))
      exec ('a' |\=| char "x") `shouldBe` Not (CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char)))
      exec (char "x" |\=| 'a') `shouldBe` Not (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'a'))
      exec (char "x" |\=| char "y") `shouldBe`
        Not (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)))

  describe "the `is` predicate" $ do
    let exec = execGoalWriter
    it "should create an Identical goal from TermData" $ do
      exec ('a' `is` 'b') `shouldBe` Identical (toTerm 'a') (toTerm 'b')
      exec ('a' `is` char "x") `shouldBe` Identical (toTerm 'a') (toTerm (Var "x" :: Var Char))
      exec (char "x" `is` 'a') `shouldBe` Identical (toTerm (Var "x" :: Var Char)) (toTerm 'a')
      exec (char "x" `is` char "y") `shouldBe`
        Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))
  describe "the `isnt` predicate" $ do
    let exec = execGoalWriter
    it "should create a (Not . Identical) goal from TermData" $ do
      exec ('a' `isnt` 'b') `shouldBe` Not (Identical (toTerm 'a') (toTerm 'b'))
      exec ('a' `isnt` char "x") `shouldBe` Not (Identical (toTerm 'a') (toTerm (Var "x" :: Var Char)))
      exec (char "x" `isnt` 'a') `shouldBe` Not (Identical (toTerm (Var "x" :: Var Char)) (toTerm 'a'))
      exec (char "x" `isnt` char "y") `shouldBe`
        Not (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)))

  describe "the |==| predicate" $ do
    let exec = execGoalWriter
    it "should create an Equal goal from two terms" $ do
      exec ((3 :: Int) |==| (3 :: Int)) `shouldBe` Equal (toTerm (3 :: Int)) (toTerm (3 :: Int))
      exec (int "x" |==| (3 :: Int)) `shouldBe` Equal (toTerm (Var "x" :: Var Int)) (toTerm (3 :: Int))
    it "should have lower precedence than arithmetic operators" $
      exec (int "x" |==| (3 :: Int) |+| (2 :: Int)) `shouldBe`
        Equal (toTerm (Var "x" :: Var Int)) (Ast.Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))
  describe "the |\\==| predicate" $ do
    let exec = execGoalWriter
    it "should create a (Not . Equal) goal from two terms" $ do
      exec ((3 :: Int) |\==| (3 :: Int)) `shouldBe`
        Not (Equal (toTerm (3 :: Int)) (toTerm (3 :: Int)))
      exec (int "x" |\==| (3 :: Int)) `shouldBe`
        Not (Equal (toTerm (Var "x" :: Var Int)) (toTerm (3 :: Int)))
    it "should have lower precedence than arithmetic operators" $
      exec (int "x" |\==| (3 :: Int) |+| (2 :: Int)) `shouldBe`
        Not (Equal (toTerm (Var "x" :: Var Int)) (Ast.Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))))

  describe "the |<| predicate" $ do
    let exec = execGoalWriter
    it "should create a LessThan goal from two terms" $
      exec ('a' |<| 'b') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |<| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        LessThan (toTerm (1 :: Int)) (Ast.Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
  describe "the |>| predicate" $ do
    let exec = execGoalWriter
    it "should reorder the terms to create a LessThan goal" $
      exec ('b' |>| 'a') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |>| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        LessThan (Ast.Sum (toTerm (2 :: Int)) (toTerm (3 :: Int))) (toTerm (1 :: Int))
  describe "the |<=| predicate" $ do
    let exec = execGoalWriter
    it "should succeed if the terms are equal" $ do
      let sols = runHspl $ 'a' |<=| 'a'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` execGoalWriter ('a' |<=| 'a')
    it "should succeed if the left-hand side is less than the right-hand side" $ do
      let sols = runHspl $ 'a' |<=| 'b'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` execGoalWriter ('a' |<=| 'b')
    it "should unify variables on the left-hand side if possible" $ do
      let sols = runHspl $ char "x" |<=| 'a'
      length sols `shouldBe` 1
      queryVar (head sols) (char "x") `shouldBe` Unified 'a'
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |<=| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        exec ((1 :: Int) |<=| ((2 :: Int) |+| (3 :: Int)))
  describe "the |>=| predicate" $ do
    let exec = execGoalWriter
    it "should succeed if the terms are equal" $ do
      let sols = runHspl $ 'a' |>=| 'a'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` execGoalWriter ('a' |>=| 'a')
    it "should succeed if the left-hand side is greater than the right-hand side" $ do
      let sols = runHspl $ 'b' |>=| 'a'
      length sols `shouldBe` 1
      getTheorem (head sols) `shouldBe` execGoalWriter ('b' |>=| 'a')
    it "should unify variables on the left-hand side if possible" $ do
      let sols = runHspl $ char "x" |>=| 'a'
      length sols `shouldBe` 1
      queryVar (head sols) (char "x") `shouldBe` Unified 'a'
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |>=| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        exec ((1 :: Int) |>=| ((2 :: Int) |+| (3 :: Int)))

  describe "the ||| predicate" $ do
    let exec = execGoalWriter
    it "should create an Or goal from two goals" $
      exec (foo? 'a' ||| foo? 'b') `shouldBe`
        Or (PredGoal (Ast.predicate "foo" 'a') fooDefs) (PredGoal (Ast.predicate "foo" 'b') fooDefs)
    it "should permit nested expressions" $
      exec (foo? 'a' ||| do {foo? 'b'; foo? 'c'}) `shouldBe`
        Or (PredGoal (Ast.predicate "foo" 'a') fooDefs)
           (And (PredGoal (Ast.predicate "foo" 'b') fooDefs)
                (PredGoal (Ast.predicate "foo" 'c') fooDefs))

  describe "the true predicate" $
    it "should create a Top goal" $
      execGoalWriter true `shouldBe` Top
  describe "the false predicate" $
    it "should create a Bottom goal" $
      execGoalWriter false `shouldBe` Bottom

  describe "the forAll predicate" $ do
    let testSuccess c a = getAllTheorems (runHspl $ forAll c a) `shouldBe`
            [execGoalWriter $ forAll c a]
    it "should succeed if the condition fails" $
      testSuccess false false
    it "should succeed when the condition succeeds and the action always succeeds" $ do
      testSuccess true true
      testSuccess (int "x" |=| (3::Int) ||| int "x" |=| (2::Int) |+| (1::Int)) ((3::Int) |==| v"x")
    it "should fail when any of the actions fail" $
      runHspl (forAll (enum? (v"x" :: Var BoundedEnum)) (v"x" |=| E1)) `shouldBe` []
    it "should not bind any variables" $ do
      let results = runHspl $ forAll (v"x" |=| 'a') true
      length results `shouldBe` 1
      queryVar (head results) (char "x") `shouldBe` Ununified

      let results = runHspl $ forAll true (v"x" |=| 'a')
      length results `shouldBe` 1
      queryVar (head results) (char "x") `shouldBe` Ununified

  describe "arithmetic operators" $ do
    it "should create a sum of terms" $ do
      ((3 :: Int) |+| (2 :: Int)) `shouldBe`
        Ast.Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" |+| (2 :: Int)) `shouldBe`
        Ast.Sum (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a difference of terms" $ do
      ((3 :: Int) |-| (2 :: Int)) `shouldBe`
        Ast.Difference (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" |-| (2 :: Int)) `shouldBe`
        Ast.Difference (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a product of terms" $ do
      ((3 :: Int) |*| (2 :: Int)) `shouldBe`
        Ast.Product (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" |*| (2 :: Int)) `shouldBe`
        Ast.Product (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a quotient of fractionals" $ do
      ((3 :: Double) |/| (2 :: Double)) `shouldBe`
        Ast.Quotient (toTerm (3 :: Double)) (toTerm (2 :: Double))
      (double "x" |/| (2 :: Double)) `shouldBe`
        Ast.Quotient (toTerm (Var "x" :: Var Double)) (toTerm (2 :: Double))
    it "should create a quotient of integrals" $ do
      ((3 :: Int) |\| (2 :: Int)) `shouldBe`
        Ast.IntQuotient (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" |\| (2 :: Int)) `shouldBe`
        Ast.IntQuotient (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should create a modular expression" $ do
      ((3 :: Int) |%| (2 :: Int)) `shouldBe`
        Ast.Modulus (toTerm (3 :: Int)) (toTerm (2 :: Int))
      (int "x" |%| (2 :: Int)) `shouldBe`
        Ast.Modulus (toTerm (Var "x" :: Var Int)) (toTerm (2 :: Int))
    it "should be left-associative" $ do
      (int "x" |+| int "y" |-| int "z") `shouldBe`
        Ast.Difference (Ast.Sum (toTerm (Var "x" :: Var Int))
                                (toTerm (Var "y" :: Var Int)))
                       (toTerm (Var "z" :: Var Int))
      (int "x" |*| int "y" |\| int "z") `shouldBe`
        Ast.IntQuotient (Ast.Product (toTerm (Var "x" :: Var Int))
                                     (toTerm (Var "y" :: Var Int)))
                        (toTerm (Var "z" :: Var Int))
      (double "x" |*| double "y" |/| double "z") `shouldBe`
        Ast.Quotient (Ast.Product (toTerm (Var "x" :: Var Double))
                                  (toTerm (Var "y" :: Var Double)))
                     (toTerm (Var "z" :: Var Double))
      (int "x" |%| int "y" |%| int "z") `shouldBe`
        Ast.Modulus (Ast.Modulus (toTerm (Var "x" :: Var Int))
                                 (toTerm (Var "y" :: Var Int)))
                    (toTerm (Var "z" :: Var Int))
    it "should give multiplication and division higher precedence than addition and subtraction" $ do
      (int "x" |+| int "y" |*| int "z") `shouldBe`
        Ast.Sum (toTerm (Var "x" :: Var Int))
                (Ast.Product (toTerm (Var "y" :: Var Int))
                             (toTerm (Var "z" :: Var Int)))
      (int "x" |-| int "y" |\| int "z") `shouldBe`
        Ast.Difference (toTerm (Var "x" :: Var Int))
                       (Ast.IntQuotient (toTerm (Var "y" :: Var Int))
                                        (toTerm (Var "z" :: Var Int)))
      (double "x" |+| double "y" |/| double "z") `shouldBe`
        Ast.Sum (toTerm (Var "x" :: Var Double))
                (Ast.Quotient (toTerm(Var "y" :: Var Double))
                              (toTerm(Var "z" :: Var Double)))
    it "should give modulus the same precedence as multiplication" $ do
      (int "x" |*| int "y" |%| int "z") `shouldBe`
        Ast.Modulus (Ast.Product (toTerm (Var "x" :: Var Int))
                                 (toTerm (Var "y" :: Var Int)))
                    (toTerm (Var "z" :: Var Int))
      (int "x" |%| int "y" |*| int "z") `shouldBe`
        Ast.Product (Ast.Modulus (toTerm (Var "x" :: Var Int))
                                 (toTerm (Var "y" :: Var Int)))
                    (toTerm (Var "z" :: Var Int))
