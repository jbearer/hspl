{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -fdefer-type-errors #-}
#endif

module UnificationTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Unification
import Control.Hspl.Internal.VarMap (Entry (..))
import qualified Control.Hspl.Internal.VarMap as M
#if __GLASGOW_HASKELL__ >= 800
import Test.ShouldNotTypecheck
#endif

import Control.Exception.Base (evaluate)
import Control.Monad.State hiding (when)
import Control.Monad.Trans.Maybe
import Control.Monad.Writer (MonadWriter (..), runWriter)
import Data.Data
import Data.Monoid ((<>))
import Data.Typeable
import GHC.Generics

data RecursiveType = Base | Rec RecursiveType
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable RecursiveType

data TwoChars = TwoChars Char Char
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable TwoChars

type MockUnification = MaybeT (StateT Unifier VarGenerator)

instance MonadVarGenerator MockUnification where
  fresh = lift $ lift fresh

instance MonadUnification MockUnification where
  stateUnifier = lift . state

runMockUnification :: MockUnification a -> Maybe (a, Unifier)
runMockUnification m =
  let st = runMaybeT m
      (ma, u) = runVarGenerator $ runStateT st M.empty
  in case ma of
    Just a -> Just (a, u)
    Nothing -> Nothing

renameWithContext :: Renamer -> Int -> Term a -> Term a
renameWithContext renamer fresh t =
  let r = put renamer >> renameTerm t
      vg = put fresh >> runRenamedT r
  in evalState vg fresh

renamePredWithContext :: Renamer -> Int -> Predicate -> Predicate
renamePredWithContext renamer fresh p =
  let r = put renamer >> renamePredicate p
      vg = put fresh >> runRenamedT r
  in evalState vg fresh

renameGoalWithContext :: Renamer -> Int -> Goal -> Goal
renameGoalWithContext renamer fresh g =
  let r = put renamer >> renameGoal g
      vg = put fresh >> runRenamedT r
  in evalState vg fresh

doRenameClause :: HornClause -> HornClause
doRenameClause c = runVarGenerator $ renameClause c

test = describeModule "Control.Hspl.Internal.Unification" $ do
  describe "a unifier" $ do
    it "should have a singleton substitution operator" $
      True // Var "x" `shouldBe` M.singleton (Var "x") (toTerm True)
    when "empty" $ do
      it "should act as an identity of composition" $ do
        let u = toTerm True // Var "x"
        u `compose` M.empty `shouldBe` u
        M.empty `compose` u `shouldBe` u
      it "should act as an identity of unification" $ do
        let t = toTerm (Var "x" :: Var Bool)
        unify M.empty t `shouldBe` t
    it "should not allow terms to replace variables of a different type" $ do
#if __GLASGOW_HASKELL__ >= 800
      -- This should work
      evaluate $ toTerm True // (Var "x" :: Var Bool)
      -- But this should not
      shouldNotTypecheck $ toTerm True // (Var "x" :: Var Char)
#else
      pendingWith "ShouldNotTypecheck tests require GHC >= 8.0"
#endif
    it "is a subunifier of another if the other contains all of the substitutions of the first" $ do
      'a' // Var "x" `shouldSatisfy` (`isSubunifierOf` ('a' // Var "x" <> True // Var "y"))
      'a' // Var "x" <> True // Var "y" `shouldSatisfy`
        (`isSubunifierOf` ('a' // Var "x" <> True // Var "y"))
      'a' // Var "x" <> True // Var "y" `shouldSatisfy`
        (`isSubunifierOf` ('a' // Var "x" <> 'b' // Var "x'" <> True // Var "y" <> () // Var "z"))
    it "is not a subunifier of another which does not contain a substitution in the first" $
      'a' // Var "x" <> 'b' // Var "y" `shouldSatisfy` not . (`isSubunifierOf` ('a' // Var "x"))
    it "is not a subunifier of another which does not contain a submap of the first" $
      'a' // Var "x" <> True // Var "y" `shouldSatisfy` not . (`isSubunifierOf` ('a' // Var "y"))
    it "should return the unification status of a variable" $ do
      findVar M.empty (Var "x" :: Var Bool) `shouldBe` Ununified
      findVar (toTerm 'a' // Var "x") (Var "x" :: Var Bool) `shouldBe` Ununified
      findVar (toTerm True // Var "y") (Var "x" :: Var Bool) `shouldBe` Ununified
      findVar (toTerm True // Var "x") (Var "x" :: Var Bool) `shouldBe` Unified True
      let t = adt Just (Var "y" :: Var Bool)
      findVar (t // Var "x") (Var "x" :: Var (Maybe Bool)) `shouldBe` Partial t

      findVar ((Var "y" :: Var Char) // Var "x" <> 'a' // Var "y") (Var "x" :: Var Char) `shouldBe`
        Unified 'a'
      findVar ((Var "y" :: Var (Maybe Char)) // Var "x" <> adt Just (Var "z" :: Var Char) // Var "y")
              (Var "x" :: Var (Maybe Char)) `shouldBe`
        Partial (adt Just (Var "z" :: Var Char))
  describe "term unification" $ do
    context "of anonymous variables" $ do
      it "should always succeed" $ do
        mgu (toTerm Anon) (toTerm 'a') `shouldBe` Just M.empty
        mgu (toTerm 'a') (toTerm Anon) `shouldBe` Just M.empty
        mgu (toTerm (Anon :: Var Char)) (toTerm Anon) `shouldBe` Just M.empty
      it "should bind multiple anonymous variables to different values" $
        mgu (toTerm ('a', Anon)) (toTerm (Anon, 'b')) `shouldBe` Just M.empty
    when "both terms are variables" $
      it "should keep user-defined variables over fresh variables where possible" $ do
        mgu (toTerm (Var "x" :: Var Char)) (toTerm (Fresh 0 :: Var Char)) `shouldBe`
          Just (toTerm (Var "x" :: Var Char) // Fresh 0)
        mgu (toTerm (Fresh 0 :: Var Char)) (toTerm (Var "x" :: Var Char)) `shouldBe`
          Just (toTerm (Var "x" :: Var Char) // Fresh 0)
    when "one term is a variable" $ do
      it "should unify with any term" $ do
        mgu (toTerm $ Var "x") (toTerm True) `shouldBe` Just (toTerm True // Var "x")
        mgu (toTerm True) (toTerm $ Var "x") `shouldBe` Just (toTerm True // Var "x")
        mgu (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char)) `shouldBe`
          Just (toTerm (Var "y" :: Var Char) // Var "x")
        mgu (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char)) `shouldBe` Just M.empty
          -- ^ This should NOT fail the occurs check!
      it "should fail when the term being substituted contains the variable (occurs check)" $ do
        mgu (toTerm (Var "x" :: Var [Bool]))
            (List $ VarCons (toTerm True) (Var "x")) `shouldBe` Nothing
        mgu (toTerm (Var "x" :: Var RecursiveType))
            (adt Rec (Var "x" :: Var RecursiveType)) `shouldBe` Nothing
      it "should match the tail of a list" $ do
        mgu (toTerm "foo") (List $ VarCons (toTerm 'f') (Var "xs")) `shouldBe` Just (toTerm "oo" // Var "xs")
        mgu (List $ VarCons (toTerm 'f') (Var "xs")) (toTerm "foo") `shouldBe` Just (toTerm "oo" // Var "xs")

        mgu (toTerm "foo") (List $ VarCons (toTerm 'f') Anon) `shouldBe` Just M.empty
        mgu (List $ VarCons (toTerm 'f') Anon) (toTerm "foo") `shouldBe` Just M.empty
    when "both elements are constants" $ do
      it "should unify equal constants" $ do
        mgu (toTerm True) (toTerm True) `shouldBe` Just M.empty
        mgu (toTerm 'a') (toTerm 'a') `shouldBe` Just M.empty
      it "should fail to unify unequal constants" $ do
        mgu (toTerm True) (toTerm False) `shouldBe` Nothing
        mgu (toTerm 'a') (toTerm 'b') `shouldBe` Nothing
    when "both terms are tuples" $ do
      it "should unify the elements in sequence" $
        mgu (toTerm ('a', Var "x" :: Var Bool)) (toTerm (Var "y" :: Var Char, True)) `shouldBe`
          Just (toTerm 'a' // Var "y" <> toTerm True // Var "x")
      it "should fail to unify if any element fails" $ do
        mgu (toTerm ('a', Var "x" :: Var Char)) (toTerm ('b', 'c')) `shouldBe` Nothing
        mgu (toTerm (Var "x" :: Var Char, 'a')) (toTerm ('b', 'c')) `shouldBe` Nothing
      it "should apply each intermediate unifier to the remaining terms before unifying them" $
        mgu (toTerm ('a', Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char, Var "y" :: Var Char)) `shouldBe`
          Just (toTerm 'a' // Var "x" <> toTerm 'a' // Var "y")
      it "should fail to unify tuples of different lengths" $
#if __GLASGOW_HASKELL__ >= 800
        shouldNotTypecheck $ mgu (toTerm ('a', 'b')) (toTerm ('a', 'b', Var "x" :: Var Char))
#else
        pendingWith "ShouldNotTypecheck tests require GHC >= 8.0"
#endif
    when "both terms are lists" $ do
      it "should unify the elements in sequence" $
        mgu (toTerm [toTerm 'a', toTerm (Var "x" :: Var Char)])
            (toTerm [toTerm (Var "y" :: Var Char), toTerm 'b']) `shouldBe`
          Just (toTerm 'a' // Var "y" <> toTerm 'b' // Var "x")
      it "should unify a variable with the tail of a list" $
        mgu (toTerm "abc") (List $ VarCons (toTerm 'a') (Var "xs")) `shouldBe`
          Just (toTerm "bc" // Var "xs")
      it "should fail to unify if any element fails" $ do
        mgu (toTerm [toTerm 'a', toTerm (Var "x" :: Var Char)]) (toTerm ['b', 'c']) `shouldBe` Nothing
        mgu (toTerm [toTerm (Var "x" :: Var Char), toTerm 'a']) (toTerm ['b', 'c']) `shouldBe` Nothing
      it "should apply each intermediate unifier to the remaining terms before unifying them" $
        mgu (toTerm [toTerm 'a', toTerm (Var "x" :: Var Char)])
            (toTerm [toTerm (Var "x" :: Var Char), toTerm (Var "y" :: Var Char)]) `shouldBe`
          Just (toTerm 'a' // Var "x" <> toTerm 'a' // Var "y")
      it "should fail to unify lists of different lengths" $
        mgu (toTerm ['a', 'b']) (toTerm [toTerm 'a', toTerm 'b', toTerm (Var "x" :: Var Char)]) `shouldBe`
          Nothing
    when "both terms are ADTs" $ do
      it "should unify terms with matching constructors by unifying the arguments" $ do
        mgu (adt Just 'a') (adt Just (Var "x")) `shouldBe`
          Just (toTerm 'a' // Var "x")
        mgu (adt Just (Var "x")) (adt Just 'a') `shouldBe`
          Just (toTerm 'a' // Var "x")
      it "should apply the unifier of respective arguments to subsequent arguments before unifying them" $
        mgu (adt TwoChars ('a', Var "x" :: Var Char))
            (adt TwoChars (Var "x" :: Var Char, Var "y" :: Var Char)) `shouldBe`
          Just (toTerm 'a' // Var "x" <> toTerm 'a' // Var "y")
      it "should fail to unify terms with different constructors" $ do
        mgu (adt Left 'a') (adt Right 'a') `shouldBe` Nothing
        mgu (adt Left 'a') (adt Right True) `shouldBe` Nothing
        mgu (adt Left (Var "x" :: Var Char))
            (adt Right (Var "y" :: Var Char)) `shouldBe`
          Nothing
    when "both terms are arithmetic expressions" $ do
      it "should unify terms of the same type of expression by unifying the operands" $ do
        mgu (Sum (toTerm $ Var "x") (toTerm (1 :: Int)))
            (Sum (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe`
          Just (toTerm (1 :: Int) // Var "y" <> toTerm (2 :: Int) // Var "x")
        mgu (Difference (toTerm $ Var "x") (toTerm (1 :: Int)))
            (Difference (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe`
          Just (toTerm (1 :: Int) // Var "y" <> toTerm (2 :: Int) // Var "x")
        mgu (Product (toTerm $ Var "x") (toTerm (1 :: Int)))
            (Product (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe`
          Just (toTerm (1 :: Int) // Var "y" <> toTerm (2 :: Int) // Var "x")
        mgu (Quotient (toTerm $ Var "x") (toTerm (1.0 :: Double)))
            (Quotient (toTerm (2.0 :: Double)) (toTerm $ Var "y")) `shouldBe`
          Just (toTerm (1.0 :: Double) // Var "y" <> toTerm (2.0 :: Double) // Var "x")
        mgu (IntQuotient (toTerm $ Var "x") (toTerm (1 :: Int)))
            (IntQuotient (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe`
          Just (toTerm (1 :: Int) // Var "y" <> toTerm (2 :: Int) // Var "x")
        mgu (Modulus (toTerm $ Var "x") (toTerm (1 :: Int)))
            (Modulus (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe`
          Just (toTerm (1 :: Int) // Var "y" <> toTerm (2 :: Int) // Var "x")
      it "should fail to unify different types of expressions" $ do
        mgu (Sum (toTerm $ Var "x") (toTerm (1 :: Int)))
            (Difference (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe` Nothing
        mgu (Quotient (toTerm $ Var "x") (toTerm (1.0 :: Double)))
            (Product (toTerm $ Var "x") (toTerm (1.0 :: Double))) `shouldBe` Nothing
    it "should prohibit unification of terms of different types" $ do
#if __GLASGOW_HASKELL__ >= 800
      -- This should work
      evaluate $ mgu (toTerm True) (toTerm True)
      -- but not this
      shouldNotTypecheck $ mgu (toTerm True) (toTerm 'a')
#else
      pendingWith "ShouldNotTypecheck tests require GHC >= 8.0"
#endif
  describe "term renaming" $ do
    let r = M.fromList [ Entry (Var "x" :: Var Bool) (Fresh 0)
                       , Entry (Var "x" :: Var Char) (Fresh 1)
                       , Entry (Var "y" :: Var Char) (Fresh 2)
                       , Entry (Var "z" :: Var Char) (Fresh 3)
                       ]
    let rename = renameWithContext r 4
    context "of a variable" $ do
      it "should leave anonymous variables unchanged" $
        rename (toTerm (Anon :: Var Char, Anon :: Var Char)) `shouldBe` toTerm (Anon, Anon)
      it "should replace the variable if it appears in the renamer" $ do
        rename (toTerm (Var "x" :: Var Bool)) `shouldBe` toTerm (Fresh 0 :: Var Bool)
        rename (toTerm (Var "x" :: Var Char)) `shouldBe` toTerm (Fresh 1 :: Var Char)
        rename (toTerm (Var "y" :: Var Char)) `shouldBe` toTerm (Fresh 2 :: Var Char)
        rename (toTerm (Var "z" :: Var Char)) `shouldBe` toTerm (Fresh 3 :: Var Char)
      it "should create a fresh variable if it is not in the renamer" $ do
        rename (toTerm (Var "q" :: Var Char)) `shouldBe` toTerm (Fresh 4 :: Var Char)
        rename (toTerm (Var "y" :: Var Bool)) `shouldBe` toTerm (Fresh 4 :: Var Bool)
    context "of a constant" $
      it "should return the original constant" $ do
        rename (toTerm 'a') `shouldBe` toTerm 'a'
        rename (toTerm True) `shouldBe` toTerm True
    context "of a tuple" $ do
      it "should recursively rename variables in each element" $ do
        rename (toTerm (Var "x" :: Var Bool, Var "x" :: Var Char)) `shouldBe`
          toTerm (Fresh 0 :: Var Bool, Fresh 1 :: Var Char)
        rename (toTerm (Var "x" :: Var Bool, Var "q" :: Var Char)) `shouldBe`
          toTerm (Fresh 0 :: Var Bool, Fresh 4 :: Var Char)
        rename (toTerm (Var "x" :: Var Char, (Var "y" :: Var Char, Var "z" :: Var Char))) `shouldBe`
          toTerm (Fresh 1 :: Var Char, (Fresh 2 :: Var Char, Fresh 3 :: Var Char))
      it "should rename the same variable with the same replacement" $ do
        rename (toTerm (Var "x" :: Var Bool, Var "x" :: Var Bool)) `shouldBe`
          toTerm (Fresh 0 :: Var Bool, Fresh 0 :: Var Bool)
        rename (toTerm (Var "q" :: Var Char, Var "q" :: Var Char)) `shouldBe`
          toTerm (Fresh 4 :: Var Char, Fresh 4 :: Var Char)
    context "of a list" $ do
      it "should recursively rename variables in each element" $ do
        rename (toTerm [Var "x" :: Var Char, Var "y" :: Var Char]) `shouldBe`
          toTerm [Fresh 1 :: Var Char, Fresh 2 :: Var Char]
        rename (toTerm [Var "x" :: Var Char, Var "q" :: Var Char]) `shouldBe`
          toTerm [Fresh 1 :: Var Char, Fresh 4 :: Var Char]
      it "should rename a variable in the tail of the list" $ do
        let r = M.singleton (Var "xs" :: Var String) (Fresh 0)
        renameWithContext r 1 (List $ VarCons (toTerm 'a') (Var "xs")) `shouldBe`
          List (VarCons (toTerm 'a') (Fresh 0))
      it "should rename the same variable with the same replacement" $ do
        rename (toTerm [Var "x" :: Var Bool, Var "x" :: Var Bool]) `shouldBe`
          toTerm [Fresh 0 :: Var Bool, Fresh 0 :: Var Bool]
        rename (toTerm [Var "q" :: Var Char, Var "q" :: Var Char]) `shouldBe`
          toTerm [Fresh 4 :: Var Char, Fresh 4 :: Var Char]
    context "of an ADT constructor" $ do
      it "should recursively rename variables in the argument" $ do
        rename (adt Just (Var "x" :: Var Char)) `shouldBe`
          adt Just (Fresh 1 :: Var Char)
        rename (adt Just (Var "x" :: Var Char, Var "q" :: Var Int)) `shouldBe`
          adt Just (Fresh 1 :: Var Char, Fresh 4 :: Var Int)
      it "should rename the same variable with the same replacement" $ do
        rename (adt TwoChars (Var "x" :: Var Char, Var "x" :: Var Char)) `shouldBe`
          adt TwoChars (Fresh 1 :: Var Char, Fresh 1 :: Var Char)
        rename (adt TwoChars (Var "q" :: Var Char, Var "q" :: Var Char)) `shouldBe`
          adt TwoChars (Fresh 4 :: Var Char, Fresh 4 :: Var Char)
    context "of an arithmetic expression" $ do
      it "should recursively rename variables in each operand" $ do
        rename (Sum (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Sum (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 5)
        rename (Difference (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Difference (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 5)
        rename (Product (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Product (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 5)
        rename (Quotient (toTerm (Var "x" :: Var Double)) (toTerm $ Var "y")) `shouldBe`
          Quotient (toTerm (Fresh 4 :: Var Double)) (toTerm $ Fresh 5)
        rename (IntQuotient (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          IntQuotient (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 5)
        rename (Modulus (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Modulus (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 5)
      it "should rename the same variable with the same replacement" $ do
        rename (Sum (toTerm (Var "x" :: Var Int)) (toTerm $ Var "x")) `shouldBe`
          Sum (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 4)
        rename (Difference (toTerm (Var "x" :: Var Int)) (toTerm $ Var "x")) `shouldBe`
          Difference (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 4)
        rename (Product (toTerm (Var "x" :: Var Int)) (toTerm $ Var "x")) `shouldBe`
          Product (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 4)
        rename (Quotient (toTerm (Var "x" :: Var Double)) (toTerm $ Var "x")) `shouldBe`
          Quotient (toTerm (Fresh 4 :: Var Double)) (toTerm $ Fresh 4)
        rename (IntQuotient (toTerm (Var "x" :: Var Int)) (toTerm $ Var "x")) `shouldBe`
          IntQuotient (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 4)
        rename (Modulus (toTerm (Var "x" :: Var Int)) (toTerm $ Var "x")) `shouldBe`
          Modulus (toTerm (Fresh 4 :: Var Int)) (toTerm $ Fresh 4)
  describe "predicate renaming" $ do
    let r = M.singleton (Var "x" :: Var Bool) (Fresh 0)
    let rename = renamePredWithContext r 1
    it "should rename variables in the argument if the renamer applies" $
      rename (predicate "foo" (Var "x" :: Var Bool)) `shouldBe` predicate "foo" (Fresh 0 :: Var Bool)
    it "should create fresh variables when the argument contains a variable not in the renamer" $
      rename (predicate "foo" (Var "q" :: Var Bool)) `shouldBe` predicate "foo" (Fresh 1 ::Var Bool)
  describe "goal renaming" $ do
    let rename = renameGoalWithContext M.empty 0
    context "of predicate goals" $ do
      it "should rename variables in the predicate" $
        rename (PredGoal (predicate "foo" (Var "x" :: Var Bool)) []) `shouldBe`
          PredGoal (predicate "foo" (Fresh 0 :: Var Bool)) []
      it "should ignore the clauses" $ do
        let g = PredGoal (predicate "foo" ())
                         [HornClause (predicate "bar" (Var "x" :: Var Char)) Top]
        rename g `shouldBe` g
    withParams [IsUnified, IsVariable] $ \constr ->
      context "of unary term goals" $
        it "should rename variables in the term" $
          rename (constr (toTerm (Var "x" :: Var Char))) `shouldBe` constr (toTerm $ Fresh 0)
    context "of binary term goals" $ do
      let constrs :: [Term Char -> Term Char -> Goal]
          constrs = [CanUnify, Identical, Equal, LessThan]
      withParams constrs $ \constr -> do
        it "should rename variables in each term" $
          rename (constr (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
            constr (toTerm (Fresh 0 :: Var Char)) (toTerm (Fresh 1 :: Var Char))
        it "should rename variables in both terms the same" $
          rename (constr (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
            constr (toTerm (Fresh 0 :: Var Char)) (toTerm (Fresh 0 :: Var Char))
    context "of unary outer goals" $
      withParams [Not, CutFrame, Track] $ \constr ->
        it "should rename variables in the inner goal" $
          rename (constr $ PredGoal (predicate "foo" (Var "x" :: Var Bool)) []) `shouldBe`
            constr (PredGoal (predicate "foo" (Fresh 0 :: Var Bool)) [])
    context "of binary logic goals" $
      withParams [And, Or] $ \constr -> do
        it "should rename variables in each goal" $
          rename (constr (PredGoal (predicate "foo" (Var "x" :: Var Char)) [])
                     (PredGoal (predicate "bar" (Var "y" :: Var Bool)) [])) `shouldBe`
            constr (PredGoal (predicate "foo" (Fresh 0 :: Var Char)) [])
               (PredGoal (predicate "bar" (Fresh 1 :: Var Bool)) [])
        it "should rename variables in both terms the same" $
          rename (constr (PredGoal (predicate "foo" (Var "x" :: Var Char)) [])
                     (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])) `shouldBe`
            constr (PredGoal (predicate "foo" (Fresh 0 :: Var Char)) [])
               (PredGoal (predicate "bar" (Fresh 0 :: Var Char)) [])
    context "of unitary goals" $
      withParams [Top, Bottom, Cut] $ \constr ->
        it "should be a noop" $
          rename constr `shouldBe` constr
    withParams [Nothing, Just 42] $ \n ->
      context "of Alternatives goals" $ do
        let go x g xs = rename $ Alternatives n (toTerm x) g (toTerm xs)
        it "should rename variables in each subcomponent" $
          go (Var "x" :: Var Char) (Equal (toTerm 'a') (toTerm $ Var "y")) (Var "xs") `shouldBe`
            go (Fresh 0 :: Var Char) (Equal (toTerm 'a') (toTerm $ Fresh 1)) (Fresh 2)
        it "should rename the same variables the same way" $
          go (Var "x" :: Var Char)
             (PredGoal (predicate "foo" (Var "x" :: Var Char, Var "xs" :: Var [Char])) [])
             (Var "xs") `shouldBe`
            go (Fresh 0 :: Var Char)
               (PredGoal (predicate "foo" (Fresh 0 :: Var Char, Fresh 1 :: Var [Char])) [])
               (Fresh 1)
  describe "clause renaming" $ do
    let rename = doRenameClause
    it "should rename variables in the positive literal" $
      rename (HornClause (predicate "foo" (Var "x" :: Var Bool)) Top) `shouldBe`
        HornClause (predicate "foo" (Fresh 0 :: Var Bool)) Top
    it "should rename variables in the negative literal" $
      rename (HornClause (predicate "foo" ())
                         (PredGoal (predicate "bar" (Var "x" :: Var Bool)) [])) `shouldBe`
        HornClause (predicate "foo" ())
                   (PredGoal (predicate "bar" (Fresh 0 :: Var Bool)) [])
    it "should apply renamings generated in the positive literal to the negative literal" $
      rename (HornClause (predicate "foo" (Var "q" :: Var Char, Var "p" :: Var Char))
                         (PredGoal (predicate "bar" (Var "p" :: Var Char)) [])) `shouldBe`
        HornClause (predicate "foo" (Fresh 0 :: Var Char, Fresh 1 :: Var Char))
                   (PredGoal (predicate "bar" (Fresh 1 :: Var Char)) [])
  describe "term unifier application" $ do
    context "to a variable" $ do
      it "should replace the variable if there is a corresponding substitution" $
        unify (toTerm 'a' // Var "x") (toTerm (Var "x" :: Var Char)) `shouldBe` toTerm 'a'
      it "should return the original variable if there is no substitution" $ do
        let x = toTerm (Var "x" :: Var Char)
        unify M.empty x `shouldBe` x
        unify (toTerm 'a' // Var "y") x `shouldBe` x -- No substitution for the right name
        unify (toTerm True // Var "x") x `shouldBe` x -- No substitution for the right type
    context "to a constant" $
      it "should return the original constant" $ do
        let u = toTerm 'a' // Var "x" <> toTerm True // Var "y"
        unify u (toTerm 'z') `shouldBe` toTerm 'z'
        unify u (toTerm False) `shouldBe` toTerm False
    context "to a tuple" $
      it "should recursively apply the unifier to each element" $ do
        unify (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (toTerm ("foo", Var "y" :: Var Bool, Var "x" :: Var Bool, Var "x" :: Var Char)) `shouldBe`
          toTerm ("foo", True, Var "x" :: Var Bool, 'a')
        unify (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (toTerm (Var "x" :: Var Char, ('z', Var "y" :: Var Bool))) `shouldBe`
          toTerm ('a', ('z', True))
    context "to a list" $ do
      it "should recursively apply the unifier to each element" $
        unify (toTerm 'a' // Var "x")
                  (toTerm [toTerm $ Var "x", toTerm 'b', toTerm $ Var "y"]) `shouldBe`
          toTerm [toTerm 'a', toTerm 'b', toTerm $ Var "y"]
      it "should apply the unifier to the tail of a list" $
        unify (toTerm "xyz" // Var "xs")
                  (List $ VarCons (toTerm (Var "x" :: Var Char)) (Var "xs")) `shouldBe`
          toTerm [toTerm $ Var "x", toTerm 'x', toTerm 'y', toTerm 'z']
    context "to an ADT constructor" $
      it "should recursively apply the unifier to the argument" $ do
        unify (toTerm 'a' // Var "x")
                  (adt Just (Var "x" :: Var Char)) `shouldBe`
          adt Just 'a'
        unify (toTerm 'a' // Var "x" <> toTerm 'b' // Var "y")
                  (adt TwoChars (Var "x" :: Var Char, Var "y" :: Var Char)) `shouldBe`
          adt TwoChars ('a', 'b')
    context "to an arithmetic expression" $
      it "should recursively apply the unifier to each element" $ do
        unify (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Sum (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Sum (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unify (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Difference (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Difference (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unify (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Product (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Product (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unify (toTerm (1.0 :: Double) // Var "x" <> (2.0 :: Double) // Var "y")
                  (Quotient (toTerm (Var "x" :: Var Double)) (toTerm $ Var "y")) `shouldBe`
          Quotient (toTerm (1.0 :: Double)) (toTerm (2.0 :: Double))
        unify (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (IntQuotient (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          IntQuotient (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unify (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Modulus (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Modulus (toTerm (1 :: Int)) (toTerm (2 :: Int))
    it "should apply the unifier recursively" $ do
      unify (adt Just (Var "y" :: Var Char) // Var "x" <> 'a' // Var "y")
            (toTerm (True, Var "x" :: Var (Maybe Char)))
        `shouldBe` toTerm (True, Just 'a')
      unify ((Var "ys" :: Var String) // Var "xs" <> "foo" // Var "ys")
            (List $ VarCons (toTerm 'a') (Var "xs"))
        `shouldBe` toTerm "afoo"
  describe "predicate unifier application" $ do
    it "should unify the argument when the unifier applies" $
      unify (toTerm 'a' // Var "x") (predicate "foo" (Var "x" :: Var Char)) `shouldBe`
        predicate "foo" 'a'
    it "should return the original predicate when the unifier is irrelevant" $ do
      let p = predicate "foo" (Var "x" :: Var Char)
      unify M.empty p `shouldBe` p
      unify (toTerm 'a' // Var "y") p `shouldBe` p
      unify (toTerm True // Var "x") p `shouldBe` p
  describe "goal unifier application" $ do
    context "to a predicate goal" $ do
      it "should unify the predicate" $
        unify (toTerm 'a' // Var "x")
                  (PredGoal (predicate "foo" (Var "x" :: Var Char)) []) `shouldBe`
          PredGoal (predicate "foo" 'a') []
      it "should ignore the clauses" $ do
        let g = PredGoal (predicate "foo" ()) [HornClause (predicate "bar" (Var "x" :: Var Char)) Top]
        unify (toTerm 'a' // Var "x") g `shouldBe` g
    withParams [IsUnified, IsVariable] $ \constr ->
      context "to a unary term goal" $ do
        it "should unify the term" $
          unify (toTerm 'a' // Var "x") (constr $ toTerm (Var "x" :: Var Char)) `shouldBe`
            constr (toTerm 'a')
        it "should leave the term unchanged when the unifier does not apply" $
          unify (toTerm 'a' // Var "x") (constr $ toTerm (Var "y" :: Var Char)) `shouldBe`
            constr (toTerm $ Var "y")
    context "to a binary term goal" $ do
      let constrs :: [Term Char -> Term Char -> Goal]
          constrs = [CanUnify, Identical, Equal, LessThan]
      withParams constrs $ \constr -> do
        it "should unify both terms" $
          unify (toTerm 'a' // Var "x" <> toTerm 'b' // Var "y")
            (constr (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
            constr (toTerm 'a') (toTerm 'b')
        it "should leave either term unchanged when the unifier does not apply" $ do
          let u = toTerm 'a' // Var "x"
          unify u (constr (toTerm (Var "y" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
            constr (toTerm (Var "y" :: Var Char)) (toTerm 'a')
          unify u (constr (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
            constr (toTerm 'a') (toTerm (Var "y" :: Var Char))
    context "to a unary outer goal" $
      withParams [Not, CutFrame, Track] $ \constr ->
        it "should unify the inner goal" $
          unify (toTerm 'a' // Var "x")
                    (constr $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []) `shouldBe`
            constr (PredGoal (predicate "foo" 'a') [])
    context "to a binary logic goal" $
      withParams [And, Or] $ \constr ->
        it "should unify both inner goals" $
          unify (toTerm 'a' // Var "x")
                    (constr (PredGoal (predicate "foo" (Var "x" :: Var Char)) [])
                            (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])) `shouldBe`
            constr (PredGoal (predicate "foo" 'a') []) (PredGoal (predicate "bar" 'a') [])
    context "to a unitary goal" $
      withParams [Top, Bottom, Cut] $ \constr ->
        it "should be a noop" $
          unify (toTerm 'a' // Var "x") constr `shouldBe` constr
    withParams [Nothing, Just 42] $ \n ->
      context "to an Alternatives goal" $
        it "should unify each subcomponent" $
          unify (toTerm 'a' // Var "x" <> toTerm "foo" // Var "xs")
                    (Alternatives n (toTerm (Var "x" :: Var Char))
                                    (Equal (toTerm 'a') (toTerm $ Var "x"))
                                    (toTerm $ Var "xs")) `shouldBe`
            Alternatives n (toTerm 'a') (Equal (toTerm 'a') (toTerm 'a')) (toTerm "foo")
  describe "clause unifier application" $ do
    it "should unify the positive literal when the unifier applies" $
      unify (toTerm 'a' // Var "x")
                  (HornClause (predicate "foo" (Var "x" :: Var Char)) Top) `shouldBe`
        HornClause (predicate "foo" 'a') Top
    it "should unify the negative literal when the unifier applies" $
      unify (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (HornClause (predicate "foo" ())
                              (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])) `shouldBe`
        HornClause (predicate "foo" ()) (PredGoal (predicate "bar" 'a') [])
    it "should leave the positive literal unchanged when the unifier does not apply" $ do
      let c = HornClause (predicate "foo" (Var "x" :: Var Char)) Top
      unify M.empty c `shouldBe` c
      unify (toTerm 'a' // Var "y") c `shouldBe` c
      unify (toTerm True // Var "x") c `shouldBe` c
    it "should leave the negative literal unchanged when the unifier does not apply" $ do
      let c = HornClause (predicate "foo" ()) (PredGoal (predicate "bar" (Var "x" :: Var Bool)) [])
      unify (toTerm True // Var "y") c `shouldBe` c
  describe "resolution" $ do
    let runTest p c = runMockUnification (resolve p c)
    it "should rename variables in the clause" $
      runTest (predicate "foo" ())
            (HornClause (predicate "foo" ())
                        (PredGoal (predicate "bar" (Var "x" :: Var Bool)) [])) `shouldBe`
        Just (PredGoal (predicate "bar" (Fresh 0 :: Var Bool)) [], M.empty)
    it "should return any unifications made" $
      runTest (predicate "foo" ('a', Var "x" :: Var Bool))
            (HornClause (predicate "foo" (Var "y" :: Var Char, True)) Top) `shouldBe`
        Just (Top, toTerm 'a' // Fresh 0 <> toTerm True // Var "x")
    it "should apply the unifier to variables in the clause" $
      runTest (predicate "foo" 'a')
            (HornClause (predicate "foo" (Var "x" :: Var Char))
                        (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])) `shouldBe`
        Just (PredGoal (predicate "bar" 'a') [], toTerm 'a' // Fresh 0)
    it "should not apply the unifier to renamed variables" $
      runTest (predicate "foo" (Var "x" :: Var Char))
            (HornClause (predicate "foo" 'a')
                        (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])) `shouldBe`
        Just (PredGoal (predicate "bar" (Fresh 0 :: Var Char)) [], toTerm 'a' // Var "x")
    it "should fail when the goal does not unify with the clause" $
      runTest (predicate "foo" 'a') (HornClause (predicate "foo" 'b') Top) `shouldBe` Nothing
