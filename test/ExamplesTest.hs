module ExamplesTest where

import Testing
import Control.Hspl
import Control.Hspl.Examples

test = describeModule "Control.Hspl.Examples" $ do
  describe "syllogism" $
    it "should deduce that Hypatia is human" $
      getAllTheorems (runHspl $ mortal? v"x") `shouldBe` [mortal? "hypatia"]
  describe "adts" $ do
    it "should characterize good widgets" $
      getAllTheorems (runHspl $ goodWidget? (Wuzzle $$ string "x")) `shouldBe`
        [goodWidget? (Wuzzle $$ "foo")]
    it "should fail to find good Gibbers" $
      getAllTheorems (runHspl $ goodWidget? (Gibber $$ int "x")) `shouldBe` []
  describe "lists" $ do
    it "should find all distinct members of [1, 1]" $
      getAllTheorems (runHspl $ distinct? (int "x", [1, 1] :: [Int])) `shouldBe`
        [distinct? (1 :: Int, [1, 1] :: [Int])]
    it "should compute the cross-product of two lists" $
      getAllTheorems (runHspl $ cross? (['a',  'b'], [True, False], v"xs")) `shouldBe`
        [ cross? (['a', 'b'], [True, False], ('a', True))
        , cross? (['a', 'b'], [True, False], ('a', False))
        , cross? (['a', 'b'], [True, False], ('b', True))
        , cross? (['a', 'b'], [True, False], ('b', False))
        ]
  describe "equals" $ do
    it "should indicate that a variable is not unified with a string" $
      getAllTheorems (runHspl $ isFoo? string "x") `shouldBe` []
    it "should indicate that two strings are identical" $
      getAllTheorems (runHspl $ isFoo? "foo") `shouldBe` [isFoo? "foo"]
    it "should unify a variable with a string" $
      getAllTheorems (runHspl $ couldBeFoo? string "x") `shouldBe`
        [couldBeFoo? "foo"]
  describe "odds" $
    it "should compute the first n odd numbers" $
      getAllTheorems (runHsplN 5 $ odds? int "x") `shouldBe`
        [ odds? (1 :: Int)
        , odds? (3 :: Int)
        , odds? (5 :: Int)
        , odds? (7 :: Int)
        , odds? (9 :: Int)
        ]
