module SyntaxTest where

import Testing
import Control.Hspl.Internal.Syntax
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.UI

import Control.Monad.Writer

test = describeModule "Control.Hspl.Internal.Syntax" $ do
  describe "GoalWriter" $ do
    it "should compare according to the contained goal" $ do
      (tell Top :: GoalWriter ()) `shouldBe` tell Top
      (tell (CanUnify (toTerm 'a') (toTerm $ Var "x")) :: GoalWriter ()) `shouldBe`
        tell (CanUnify (toTerm 'a') (toTerm $ Var "x"))

      (tell Top :: GoalWriter ()) `shouldNotEqual` tell Bottom
      (tell (CanUnify (toTerm 'a') (toTerm 'b')) :: GoalWriter ()) `shouldNotEqual`
        tell (CanUnify (toTerm 'a') (toTerm $ Var "x"))
    it "should Show by formatting the contained goal" $ do
      show (tell Top :: GoalWriter ()) `shouldBe` formatGoal Top
      show (tell $ CanUnify (toTerm 'a') (toTerm $ Var "x") :: GoalWriter ()) `shouldBe`
        formatGoal (CanUnify (toTerm 'a') (toTerm $ Var "x"))
  describe "astGoal" $
    it "should be the inverse of tell" $
      astGoal (tell Top) `shouldBe` Top
  describe "astClause" $
    it "should return a list of clause constructors" $
      map ($"foo") (astClause (tell [ \s -> HornClause (predicate s 'a') Top
                                    , \s -> HornClause (predicate s 'b') Top
                                    ])) `shouldBe`
        [ HornClause (predicate "foo" 'a') Top
        , HornClause (predicate "foo" 'b') Top
        ]
  describe "execCond" $
    it "should return a list of cond branches" $ do
      let top = tell Top
      let bottom = tell Bottom
      let branches = [Branch top bottom, Branch bottom top]
      execCond (tell branches) `shouldBe` branches
