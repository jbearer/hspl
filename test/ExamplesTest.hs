module ExamplesTest where

import Testing
import Control.Hspl
import Control.Hspl.Examples
import Control.Hspl.Internal.Ast (predicate)

test = describeModule "Control.Hspl.Examples" $ do
  describe "syllogism" $
    it "should deduce that Hypatia is human" $
      getAllSolutions (runHspl syllogism $ "mortal"? string "x") `shouldBe`
        [predicate "mortal" "hypatia"]
  describe "adts" $ do
    it "should characterize good widgets" $
      getAllSolutions (runHspl adts $ "goodWidget"? (Wuzzle $$ string "x")) `shouldBe`
        [predicate "goodWidget" (Wuzzle $$ "foo")]
    it "should fail to find good Gibbers" $
      getAllSolutions (runHspl adts $ "goodWidget"? (Gibber $$ int "x")) `shouldBe` []
  describe "lists" $ do
    it "should find all members of [1, 2, 3]" $
      getAllSolutions (runHspl lists $ "member"? (int "x", [1, 2, 3] :: [Int])) `shouldBe`
        [ predicate "member" (1 :: Int, [1, 2, 3] :: [Int])
        , predicate "member" (2 :: Int, [1, 2, 3] :: [Int])
        , predicate "member" (3 :: Int, [1, 2, 3] :: [Int])
        ]
    it "should find all (not necessarily distinct) members of [1, 1]" $
      getAllSolutions (runHspl lists $ "member"? (int "x", [1, 1] :: [Int])) `shouldBe`
        [ predicate "member" (1 :: Int, [1, 1] :: [Int])
        , predicate "member" (1 :: Int, [1, 1] :: [Int])
        ]
    it "should find all distinct members of [1, 1]" $
      getAllSolutions (runHspl lists $ "distinct"? (int "x", [1, 1] :: [Int])) `shouldBe`
        [predicate "distinct" (1 :: Int, [1, 1] :: [Int])]
  describe "equals" $ do
    it "should indicate that a variable is not unified with a string" $
      getAllSolutions (runHspl equals $ "isFoo"? string "x") `shouldBe` []
    it "should indicate that two strings are identical" $
      getAllSolutions (runHspl equals $ "isFoo"? "foo") `shouldBe` [predicate "isFoo" "foo"]
    it "should unify a variable with a string" $
      getAllSolutions (runHspl equals $ "couldBeFoo"? string "x") `shouldBe`
        [predicate "couldBeFoo" "foo"]
  describe "odds" $
    it "should compute the first n odd numbers" $
      getAllSolutions (runHsplN 5 odds $ "odd"? int "x") `shouldBe`
        [ predicate "odd" (1 :: Int)
        , predicate "odd" (3 :: Int)
        , predicate "odd" (5 :: Int)
        , predicate "odd" (7 :: Int)
        , predicate "odd" (9 :: Int)
        ]
