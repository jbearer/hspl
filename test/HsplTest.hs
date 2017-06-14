{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HsplTest where

import Testing
import Control.Hspl
import qualified Control.Hspl.Internal.Ast as Ast
import           Control.Hspl.Internal.Ast (Goal (..))
import qualified Control.Hspl.Internal.Solver as Solver
import           Control.Hspl.Internal.Unification ((//))

import Control.Monad.Writer
import Data.Data
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
    let exec = execWriter . unGW
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
    let run w = map ($name) $ execWriter $ unCW w
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

  describe "list term construction" $ do
    context "via cons" $ do
      it "should prepend a value to a list variable" $
        'a' <:> Var "x" `shouldBe` Ast.List (toTerm 'a') (toTerm (Var "x" :: Var String))
      it "should prepend a variable to a list" $
        char "x" <:> "foo" `shouldBe` Ast.List (toTerm (Var "x" :: Var Char)) (toTerm "foo")
      it "should be right associative" $
        char "x" <:> char "y" <:> "foo" `shouldBe`
          Ast.List (toTerm (Var "x" :: Var Char))
                   (Ast.List (toTerm (Var "y" :: Var Char)) (toTerm "foo"))
      it "should prepend a variable to a list variable" $
        char "x" <:> char \* "xs" `shouldBe`
          Ast.List (toTerm (Var "x" :: Var Char)) (toTerm (Var "xs" :: Var String))
    context "via concatenation" $ do
      it "should append a list of variables" $
        "ab" <++> [char "x", char "y"] `shouldBe`
          Ast.List (toTerm 'a') (Ast.List
                   (toTerm 'b') (Ast.List
                   (toTerm (Var "x" :: Var Char)) (Ast.List
                   (toTerm (Var "y" :: Var Char))
                   Ast.Nil)))
      it "should prepend a list of variables" $
        [char "x", char "y"] <++> "ab" `shouldBe`
          Ast.List (toTerm (Var "x" :: Var Char)) (Ast.List
                   (toTerm (Var "y" :: Var Char)) (Ast.List
                   (toTerm 'a') (Ast.List
                   (toTerm 'b')
                   Ast.Nil)))

  describe "the |=| predicate" $ do
    let exec = execWriter . unGW
    it "should create a CanUnify goal from TermData" $ do
      exec ('a' |=| 'b') `shouldBe` CanUnify (toTerm 'a') (toTerm 'b')
      exec ('a' |=| char "x") `shouldBe` CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char))
      exec (char "x" |=| 'a') `shouldBe` CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'a')
      exec (char "x" |=| char "y") `shouldBe`
        CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))
  describe "the |\\=| predicate" $ do
    let exec = execWriter . unGW
    it "should create a (Not . CanUnify) goal from TermData" $ do
      exec ('a' |\=| 'b') `shouldBe` Not (CanUnify (toTerm 'a') (toTerm 'b'))
      exec ('a' |\=| char "x") `shouldBe` Not (CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char)))
      exec (char "x" |\=| 'a') `shouldBe` Not (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm 'a'))
      exec (char "x" |\=| char "y") `shouldBe`
        Not (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)))

  describe "the `is` predicate" $ do
    let exec = execWriter . unGW
    it "should create an Identical goal from TermData" $ do
      exec ('a' `is` 'b') `shouldBe` Identical (toTerm 'a') (toTerm 'b')
      exec ('a' `is` char "x") `shouldBe` Identical (toTerm 'a') (toTerm (Var "x" :: Var Char))
      exec (char "x" `is` 'a') `shouldBe` Identical (toTerm (Var "x" :: Var Char)) (toTerm 'a')
      exec (char "x" `is` char "y") `shouldBe`
        Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))
  describe "the `isnt` predicate" $ do
    let exec = execWriter . unGW
    it "should create a (Not . Identical) goal from TermData" $ do
      exec ('a' `isnt` 'b') `shouldBe` Not (Identical (toTerm 'a') (toTerm 'b'))
      exec ('a' `isnt` char "x") `shouldBe` Not (Identical (toTerm 'a') (toTerm (Var "x" :: Var Char)))
      exec (char "x" `isnt` 'a') `shouldBe` Not (Identical (toTerm (Var "x" :: Var Char)) (toTerm 'a'))
      exec (char "x" `isnt` char "y") `shouldBe`
        Not (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)))

  describe "the |==| predicate" $ do
    let exec = execWriter . unGW
    it "should create an Equal goal from two terms" $ do
      exec ((3 :: Int) |==| (3 :: Int)) `shouldBe` Equal (toTerm (3 :: Int)) (toTerm (3 :: Int))
      exec (int "x" |==| (3 :: Int)) `shouldBe` Equal (toTerm (Var "x" :: Var Int)) (toTerm (3 :: Int))
    it "should have lower precedence than arithmetic operators" $
      exec (int "x" |==| (3 :: Int) |+| (2 :: Int)) `shouldBe`
        Equal (toTerm (Var "x" :: Var Int)) (Ast.Sum (toTerm (3 :: Int)) (toTerm (2 :: Int)))
  describe "the |\\==| predicate" $ do
    let exec = execWriter . unGW
    it "should create a (Not . Equal) goal from two terms" $ do
      exec ((3 :: Int) |\==| (3 :: Int)) `shouldBe`
        Not (Equal (toTerm (3 :: Int)) (toTerm (3 :: Int)))
      exec (int "x" |\==| (3 :: Int)) `shouldBe`
        Not (Equal (toTerm (Var "x" :: Var Int)) (toTerm (3 :: Int)))
    it "should have lower precedence than arithmetic operators" $
      exec (int "x" |\==| (3 :: Int) |+| (2 :: Int)) `shouldBe`
        Not (Equal (toTerm (Var "x" :: Var Int)) (Ast.Sum (toTerm (3 :: Int)) (toTerm (2 :: Int))))

  describe "the |<| predicate" $ do
    let exec = execWriter . unGW
    it "should create a LessThan goal from two terms" $
      exec ('a' |<| 'b') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |<| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        LessThan (toTerm (1 :: Int)) (Ast.Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
  describe "the |>| predicate" $ do
    let exec = execWriter . unGW
    it "should reorder the terms to create a LessThan goal" $
      exec ('b' |>| 'a') `shouldBe` LessThan (toTerm 'a') (toTerm 'b')
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |>| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        LessThan (Ast.Sum (toTerm (2 :: Int)) (toTerm (3 :: Int))) (toTerm (1 :: Int))
  describe "the |<=| predicate" $ do
    let exec = execWriter . unGW
    it "should succeed if the terms are equal" $ do
      let sols = runHspl $ 'a' |<=| 'a'
      length sols `shouldBe` 1
      searchProof (head sols) (Equal (toTerm 'a') (toTerm 'a')) `shouldBe`
        [Equal (toTerm 'a') (toTerm 'a')]
    it "should succeed if the left-hand side is less than the right-hand side" $ do
      let sols = runHspl $ 'a' |<=| 'b'
      length sols `shouldBe` 1
      searchProof (head sols) (LessThan (toTerm 'a') (toTerm 'b')) `shouldBe`
        [LessThan (toTerm 'a') (toTerm 'b')]
    it "should unify variables on the left-hand side if possible" $
      getAllUnifiers (runHspl $ char "x" |<=| 'a') `shouldBe` ['a' // Var "x"]
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |<=| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        exec ((1 :: Int) |<=| ((2 :: Int) |+| (3 :: Int)))
  describe "the |>=| predicate" $ do
    let exec = execWriter . unGW
    it "should succeed if the terms are equal" $ do
      let sols = runHspl $ 'a' |>=| 'a'
      length sols `shouldBe` 1
      searchProof (head sols) (Equal (toTerm 'a') (toTerm 'a')) `shouldBe`
        [Equal (toTerm 'a') (toTerm 'a')]
    it "should succeed if the left-hand side is greater than the right-hand side" $ do
      let sols = runHspl $ 'b' |>=| 'a'
      length sols `shouldBe` 1
      searchProof (head sols) (LessThan (toTerm 'a') (toTerm 'b')) `shouldBe`
        [LessThan (toTerm 'a') (toTerm 'b')]
    it "should unify variables on the left-hand side if possible" $
      getAllUnifiers (runHspl $ char "x" |>=| 'a') `shouldBe` ['a' // Var "x"]
    it "should have lower precedence than arithmetic operators" $
      exec ((1 :: Int) |>=| (2 :: Int) |+| (3 :: Int)) `shouldBe`
        exec ((1 :: Int) |>=| ((2 :: Int) |+| (3 :: Int)))

  describe "the lnot predicate" $
    it "should create a Not goal from an inner goal" $
      execWriter (unGW (lnot $ foo? 'a')) `shouldBe` Not (PredGoal (Ast.predicate "foo" 'a') fooDefs)

  describe "the ||| predicate" $ do
    let exec = execWriter . unGW
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
      execWriter (unGW true) `shouldBe` Top
  describe "the false predicate" $
    it "should create a Bottom goal" $
      execWriter (unGW false) `shouldBe` Bottom

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
