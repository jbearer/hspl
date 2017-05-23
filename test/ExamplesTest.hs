module ExamplesTest where

import Testing
import Control.Hspl hiding (predicate)
import Control.Hspl.Examples
import Control.Hspl.Internal.Ast (predicate, Goal (..))

test = describeModule "Control.Hspl.Examples" $ do
  describe "syllogism" $
    it "should deduce that Hypatia is human" $
      getAllSolutions (runHspl $ mortal? v"x") `shouldBe`
        [PredGoal (predicate "mortal" "hypatia") []]
  describe "adts" $ do
    it "should characterize good widgets" $
      getAllSolutions (runHspl $ goodWidget? (Wuzzle $$ string "x")) `shouldBe`
        [PredGoal (predicate "goodWidget" (Wuzzle $$ "foo")) []]
    it "should fail to find good Gibbers" $
      getAllSolutions (runHspl $ goodWidget? (Gibber $$ int "x")) `shouldBe` []
  describe "lists" $ do
    it "should find all members of ['a', 'b', 'c']" $
      getAllSolutions (runHspl $ member? (char "x", "abc")) `shouldBe`
        [ PredGoal (predicate "member" ('a', ['a', 'b', 'c'])) []
        , PredGoal (predicate "member" ('b', ['a', 'b', 'c'])) []
        , PredGoal (predicate "member" ('c', ['a', 'b', 'c'])) []
        ]
    it "should find all (not necessarily distinct) members of [1, 1]" $
      getAllSolutions (runHspl $ member? (int "x", [1, 1] :: [Int])) `shouldBe`
        [ PredGoal (predicate "member" (1 :: Int, [1, 1] :: [Int])) []
        , PredGoal (predicate "member" (1 :: Int, [1, 1] :: [Int])) []
        ]
    it "should find all distinct members of [1, 1]" $
      getAllSolutions (runHspl $ distinct? (int "x", [1, 1] :: [Int])) `shouldBe`
        [PredGoal (predicate "distinct" (1 :: Int, [1, 1] :: [Int])) []]
  describe "equals" $ do
    it "should indicate that a variable is not unified with a string" $
      getAllSolutions (runHspl $ isFoo? string "x") `shouldBe` []
    it "should indicate that two strings are identical" $
      getAllSolutions (runHspl $ isFoo? "foo") `shouldBe` [PredGoal (predicate "isFoo" "foo") []]
    it "should unify a variable with a string" $
      getAllSolutions (runHspl $ couldBeFoo? string "x") `shouldBe`
        [PredGoal (predicate "couldBeFoo" "foo") []]
  describe "odds" $ do
    it "should compute the first n odd numbers" $
      getAllSolutions (runHsplN 5 $ odds? int "x") `shouldBe`
        [ PredGoal (predicate "odds" (1 :: Int)) []
        , PredGoal (predicate "odds" (3 :: Int)) []
        , PredGoal (predicate "odds" (5 :: Int)) []
        , PredGoal (predicate "odds" (7 :: Int)) []
        , PredGoal (predicate "odds" (9 :: Int)) []
        ]
