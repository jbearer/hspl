{-# LANGUAGE DeriveDataTypeable #-}

module HsplTest where

import Testing
import Control.Hspl
import qualified Control.Hspl.Internal.Ast as Ast
import qualified Control.Hspl.Internal.Solver as Solver

import Control.Monad.Writer
import Data.Data
import Data.Tuple.Curry

data Arities = A1 Char
             | A2 Char Char
             | A3 Char Char Char
             | A4 Char Char Char Char
             | A5 Char Char Char Char Char
             | A6 Char Char Char Char Char Char
             | A7 Char Char Char Char Char Char Char
  deriving (Show, Eq, Typeable, Data)

test = describeModule "Control.Hspl" $ do
  describe "predicate application" $
    it "should convert a String and a TermData to a Goal" $ do
      execWriter ("foo"? 'a') `shouldBe` [Ast.PredGoal $ Ast.predicate "foo" 'a']
      execWriter ("foo"? (Var "x" :: Var String)) `shouldBe`
        [Ast.PredGoal $ Ast.predicate "foo" (Var "x" :: Var String)]
      execWriter ("foo"? ('a', Var "x" :: Var Char)) `shouldBe`
        [Ast.PredGoal $ Ast.predicate "foo" ('a', Var "x" :: Var Char)]
  describe "predicate forward declarations" $ do
    let foo = decl "foo" :: PredDecl (Int, [Int])
    context "in a def statement" $
      it "should allow the compiler to deduce the type of the argument" $
        execWriter (def foo? (v"x", v"xs")) `shouldBe`
          [Ast.HornClause (Ast.predicate "foo" (Var "x" :: Var Int, Var "xs" :: Var [Int])) []]
    context "in a goal" $
      it "should allow the compiler to deduce the type of the argument" $
        execWriter (foo? (v"x", v"xs")) `shouldBe`
          [Ast.PredGoal $ Ast.predicate "foo" (Var "x" :: Var Int, Var "xs" :: Var [Int])]
  describe "clause building" $ do
    it "should build a clause from a positive literal and a ClauseBuilder" $ do
      execWriter (def "foo"? (Var "x" :: Var String) |- "bar"? (Var "x" :: Var String)) `shouldBe`
        [Ast.HornClause (Ast.predicate "foo" (Var "x" :: Var String))
                        [Ast.PredGoal $ Ast.predicate "bar" (Var "x" :: Var String)]]
      execWriter (def "foo"? (Var "x" :: Var String) |- do
                    "bar"? (Var "x" :: Var String)
                    "baz"? 'b') `shouldBe`
        [Ast.HornClause ( Ast.predicate "foo" (Var "x" :: Var String))
                        [ Ast.PredGoal $ Ast.predicate "bar" (Var "x" :: Var String)
                        , Ast.PredGoal $ Ast.predicate "baz" 'b'
                        ]]
    it "should build unit clauses" $
      execWriter (def "foo"? 'a') `shouldBe` [Ast.HornClause (Ast.predicate "foo" 'a') []]
  describe "program building" $
    it "should convert a sequence of clause builders to an HSPL program" $
      hspl (do
        def "foo"? 'a'
        def "bar"? 'b'
        def "bar"? (Var "x" :: Var Char) |- "foo"? (Var "x" :: Var Char)) `shouldBe`
        Ast.addClauses [ Ast.HornClause (Ast.predicate "foo" 'a') []
                       , Ast.HornClause (Ast.predicate "bar" 'b') []
                       , Ast.HornClause (Ast.predicate "bar" (Var "x" :: Var Char))
                                        [Ast.PredGoal $ Ast.predicate "foo" (Var "x" :: Var Char)]
                       ] Ast.emptyProgram
  describe "program execution" $ do
    let program = hspl $ do
                          def "mortal"? string "x" |- "human"? string "x"
                          def "human"? "hypatia"
                          def "human"? "fred"
    it "should obtain all solutions when requested" $
      runHspl program ("mortal"? string "x") `shouldBe`
        Solver.runHspl program (Ast.predicate "mortal" (Var "x" :: Var String))
    it "should retrieve only the first solution when requested" $
      runHspl1 program ("mortal"? string "x") `shouldBe`
        Just (head $ Solver.runHsplN 1 program (Ast.predicate "mortal" (Var "x" :: Var String)))
    it "should retrieve at most the requested number of solutions" $
      runHsplN 1 program ("mortal"? string "x") `shouldBe`
        Solver.runHsplN 1 program (Ast.predicate "mortal" (Var "x" :: Var String))
    it "should handle failure gracefully" $ do
      runHspl program ("mortal"? "bob") `shouldBe` []
      runHspl1 program ("mortal"? "bob") `shouldBe` Nothing
      runHsplN 1 program ("mortal"? "bob") `shouldBe` []

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
      A1 $$ 'a' `shouldBe` Ast.Constructor A1 (Ast.toTerm 'a')
      A2 $$ ('a', 'b') `shouldBe` Ast.Constructor (uncurry A2) (Ast.toTerm ('a', 'b'))
      A3 $$ ('a', 'b', 'c') `shouldBe`
        Ast.Constructor (uncurryN A3) (Ast.toTerm ('a', 'b', 'c'))
      A4 $$ ('a', 'b', 'c', 'd') `shouldBe`
        Ast.Constructor (uncurryN A4) (Ast.toTerm ('a', 'b', 'c', 'd'))
      A5 $$ ('a', 'b', 'c', 'd', 'e') `shouldBe`
        Ast.Constructor (uncurryN A5) (Ast.toTerm ('a', 'b', 'c', 'd', 'e'))
      A6 $$ ('a', 'b', 'c', 'd', 'e', 'f') `shouldBe`
        Ast.Constructor (uncurryN A6) (Ast.toTerm ('a', 'b', 'c', 'd', 'e', 'f'))
      A7 $$ ('a', 'b', 'c', 'd', 'e', 'f', 'g') `shouldBe`
        Ast.Constructor (uncurryN A7) (Ast.toTerm ('a', 'b', 'c', 'd', 'e', 'f', 'g'))
    it "should work with variable arguments" $ do
      A1 $$ char "x" `shouldBe` Ast.Constructor A1 (Ast.toTerm (Var "x" :: Var Char))
      A2 $$ ('a', char "x") `shouldBe`
        Ast.Constructor (uncurry A2) (Ast.toTerm ('a', Var "x" :: Var Char))
    it "should produce terms which can be reified" $ do
      Ast.fromTerm (A3 $$ ('a', 'b', 'c')) `shouldBe` Just (A3 'a' 'b' 'c')
      Ast.fromTerm (A4 $$ ('a', 'b' ,'c', 'd')) `shouldBe` Just (A4 'a' 'b' 'c' 'd')

  describe "list term construction" $ do
    context "via cons" $ do
      it "should prepend a value to a list variable" $
        'a' <:> Var "x" `shouldBe` Ast.List (Ast.toTerm 'a') (Ast.toTerm (Var "x" :: Var String))
      it "should prepend a variable to a list" $
        char "x" <:> "foo" `shouldBe` Ast.List (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm "foo")
      it "should be right associative" $
        char "x" <:> char "y" <:> "foo" `shouldBe`
          Ast.List (Ast.toTerm (Var "x" :: Var Char))
                   (Ast.List (Ast.toTerm (Var "y" :: Var Char)) (Ast.toTerm "foo"))
      it "should prepend a variable to a list variable" $
        char "x" <:> char \* "xs" `shouldBe`
          Ast.List (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm (Var "xs" :: Var String))
    context "via concatenation" $ do
      it "should append a list of variables" $
        "ab" <++> [char "x", char "y"] `shouldBe`
          Ast.List (Ast.toTerm 'a') (Ast.List
                   (Ast.toTerm 'b') (Ast.List
                   (Ast.toTerm (Var "x" :: Var Char)) (Ast.List
                   (Ast.toTerm (Var "y" :: Var Char))
                   Ast.Nil)))
      it "should prepend a list of variables" $
        [char "x", char "y"] <++> "ab" `shouldBe`
          Ast.List (Ast.toTerm (Var "x" :: Var Char)) (Ast.List
                   (Ast.toTerm (Var "y" :: Var Char)) (Ast.List
                   (Ast.toTerm 'a') (Ast.List
                   (Ast.toTerm 'b')
                   Ast.Nil)))

  describe "the |=| predicate" $
    it "should create a CanUnify goal from TermData" $ do
      execWriter ('a' |=| 'b') `shouldBe` [Ast.CanUnify (Ast.toTerm 'a') (Ast.toTerm 'b')]
      execWriter ('a' |=| char "x") `shouldBe`
        [Ast.CanUnify (Ast.toTerm 'a') (Ast.toTerm (Var "x" :: Var Char))]
      execWriter (char "x" |=| 'a') `shouldBe`
        [Ast.CanUnify (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm 'a')]
      execWriter (char "x" |=| char "y") `shouldBe`
        [Ast.CanUnify (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm (Var "y" :: Var Char))]
  describe "the |\\=| predicate" $
    it "should create a (Not . CanUnify) goal from TermData" $ do
      execWriter ('a' |\=| 'b') `shouldBe` [Ast.Not $ Ast.CanUnify (Ast.toTerm 'a') (Ast.toTerm 'b')]
      execWriter ('a' |\=| char "x") `shouldBe`
        [Ast.Not $ Ast.CanUnify (Ast.toTerm 'a') (Ast.toTerm (Var "x" :: Var Char))]
      execWriter (char "x" |\=| 'a') `shouldBe`
        [Ast.Not $ Ast.CanUnify (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm 'a')]
      execWriter (char "x" |\=| char "y") `shouldBe`
        [Ast.Not $ Ast.CanUnify (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm (Var "y" :: Var Char))]

  describe "the |==| predicate" $
    it "should create an Identical goal from TermData" $ do
      execWriter ('a' |==| 'b') `shouldBe` [Ast.Identical (Ast.toTerm 'a') (Ast.toTerm 'b')]
      execWriter ('a' |==| char "x") `shouldBe`
        [Ast.Identical (Ast.toTerm 'a') (Ast.toTerm (Var "x" :: Var Char))]
      execWriter (char "x" |==| 'a') `shouldBe`
        [Ast.Identical (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm 'a')]
      execWriter (char "x" |==| char "y") `shouldBe`
        [Ast.Identical (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm (Var "y" :: Var Char))]
  describe "the |\\==| predicate" $
    it "should create a (Not . Identical) goal from TermData" $ do
      execWriter ('a' |\==| 'b') `shouldBe` [Ast.Not $ Ast.Identical (Ast.toTerm 'a') (Ast.toTerm 'b')]
      execWriter ('a' |\==| char "x") `shouldBe`
        [Ast.Not $ Ast.Identical (Ast.toTerm 'a') (Ast.toTerm (Var "x" :: Var Char))]
      execWriter (char "x" |\==| 'a') `shouldBe`
        [Ast.Not $ Ast.Identical (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm 'a')]
      execWriter (char "x" |\==| char "y") `shouldBe`
        [Ast.Not $ Ast.Identical (Ast.toTerm (Var "x" :: Var Char)) (Ast.toTerm (Var "y" :: Var Char))]

  describe "the lnot predicate" $
    it "should create a Not goal from an inner goal" $
      execWriter (lnot $ "foo"? 'a') `shouldBe` [Ast.Not $ Ast.PredGoal $ Ast.predicate "foo" 'a']

  describe "the is predicate" $ do
    it "should create an Equal goal from two terms" $ do
      execWriter ((3 :: Int) `is` (3 :: Int)) `shouldBe`
        [Ast.Equal (Ast.toTerm (3 :: Int)) (Ast.toTerm (3 :: Int))]
      execWriter (int "x" `is` (3 :: Int)) `shouldBe`
        [Ast.Equal (Ast.toTerm (Var "x" :: Var Int)) (Ast.toTerm (3 :: Int))]
    it "should have lower precedence than arithmetic operators" $
      execWriter (int "x" `is` (3 :: Int) |+| (2 :: Int)) `shouldBe`
        [Ast.Equal (Ast.toTerm (Var "x" :: Var Int))
                   (Ast.Sum (Ast.toTerm (3 :: Int)) (Ast.toTerm (2 :: Int)))]

  describe "arithmetic operators" $ do
    it "should create a sum of terms" $ do
      ((3 :: Int) |+| (2 :: Int)) `shouldBe`
        Ast.Sum (Ast.toTerm (3 :: Int)) (Ast.toTerm (2 :: Int))
      (int "x" |+| (2 :: Int)) `shouldBe`
        Ast.Sum (Ast.toTerm (Var "x" :: Var Int)) (Ast.toTerm (2 :: Int))
    it "should create a difference of terms" $ do
      ((3 :: Int) |-| (2 :: Int)) `shouldBe`
        Ast.Difference (Ast.toTerm (3 :: Int)) (Ast.toTerm (2 :: Int))
      (int "x" |-| (2 :: Int)) `shouldBe`
        Ast.Difference (Ast.toTerm (Var "x" :: Var Int)) (Ast.toTerm (2 :: Int))
    it "should create a product of terms" $ do
      ((3 :: Int) |*| (2 :: Int)) `shouldBe`
        Ast.Product (Ast.toTerm (3 :: Int)) (Ast.toTerm (2 :: Int))
      (int "x" |*| (2 :: Int)) `shouldBe`
        Ast.Product (Ast.toTerm (Var "x" :: Var Int)) (Ast.toTerm (2 :: Int))
    it "should create a quotient of fractionals" $ do
      ((3 :: Double) |/| (2 :: Double)) `shouldBe`
        Ast.Quotient (Ast.toTerm (3 :: Double)) (Ast.toTerm (2 :: Double))
      (double "x" |/| (2 :: Double)) `shouldBe`
        Ast.Quotient (Ast.toTerm (Var "x" :: Var Double)) (Ast.toTerm (2 :: Double))
    it "should create a quotient of integrals" $ do
      ((3 :: Int) |\| (2 :: Int)) `shouldBe`
        Ast.IntQuotient (Ast.toTerm (3 :: Int)) (Ast.toTerm (2 :: Int))
      (int "x" |\| (2 :: Int)) `shouldBe`
        Ast.IntQuotient (Ast.toTerm (Var "x" :: Var Int)) (Ast.toTerm (2 :: Int))
    it "should create a modular expression" $ do
      ((3 :: Int) |%| (2 :: Int)) `shouldBe`
        Ast.Modulus (Ast.toTerm (3 :: Int)) (Ast.toTerm (2 :: Int))
      (int "x" |%| (2 :: Int)) `shouldBe`
        Ast.Modulus (Ast.toTerm (Var "x" :: Var Int)) (Ast.toTerm (2 :: Int))
    it "should be left-associative" $ do
      (int "x" |+| int "y" |-| int "z") `shouldBe`
        Ast.Difference (Ast.Sum (Ast.toTerm (Var "x" :: Var Int))
                                (Ast.toTerm (Var "y" :: Var Int)))
                       (Ast.toTerm (Var "z" :: Var Int))
      (int "x" |*| int "y" |\| int "z") `shouldBe`
        Ast.IntQuotient (Ast.Product (Ast.toTerm (Var "x" :: Var Int))
                                     (Ast.toTerm (Var "y" :: Var Int)))
                        (Ast.toTerm (Var "z" :: Var Int))
      (double "x" |*| double "y" |/| double "z") `shouldBe`
        Ast.Quotient (Ast.Product (Ast.toTerm (Var "x" :: Var Double))
                                  (Ast.toTerm (Var "y" :: Var Double)))
                     (Ast.toTerm (Var "z" :: Var Double))
      (int "x" |%| int "y" |%| int "z") `shouldBe`
        Ast.Modulus (Ast.Modulus (Ast.toTerm (Var "x" :: Var Int))
                                 (Ast.toTerm (Var "y" :: Var Int)))
                    (Ast.toTerm (Var "z" :: Var Int))
    it "should give multiplication and division higher precedence than addition and subtraction" $ do
      (int "x" |+| int "y" |*| int "z") `shouldBe`
        Ast.Sum (Ast.toTerm (Var "x" :: Var Int))
                (Ast.Product (Ast.toTerm (Var "y" :: Var Int))
                             (Ast.toTerm (Var "z" :: Var Int)))
      (int "x" |-| int "y" |\| int "z") `shouldBe`
        Ast.Difference (Ast.toTerm (Var "x" :: Var Int))
                       (Ast.IntQuotient (Ast.toTerm (Var "y" :: Var Int))
                                        (Ast.toTerm (Var "z" :: Var Int)))
      (double "x" |+| double "y" |/| double "z") `shouldBe`
        Ast.Sum (Ast.toTerm (Var "x" :: Var Double))
                (Ast.Quotient (Ast.toTerm(Var "y" :: Var Double))
                              (Ast.toTerm(Var "z" :: Var Double)))
    it "should give modulus the same precedence as multiplication" $ do
      (int "x" |*| int "y" |%| int "z") `shouldBe`
        Ast.Modulus (Ast.Product (Ast.toTerm (Var "x" :: Var Int))
                                 (Ast.toTerm (Var "y" :: Var Int)))
                    (Ast.toTerm (Var "z" :: Var Int))
      (int "x" |%| int "y" |*| int "z") `shouldBe`
        Ast.Product (Ast.Modulus (Ast.toTerm (Var "x" :: Var Int))
                                 (Ast.toTerm (Var "y" :: Var Int)))
                    (Ast.toTerm (Var "z" :: Var Int))
