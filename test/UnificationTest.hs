{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module UnificationTest where

import Testing
import Test.ShouldNotTypecheck
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Unification

import           Control.DeepSeq        (NFData (..))
import           Control.Exception.Base (evaluate)
import           Control.Monad.State hiding (when)
import           Data.Data
import qualified Data.Map as M
import           Data.Monoid hiding (Sum, Product)
import           Data.Typeable

data RecursiveType = Base | Rec RecursiveType
  deriving (Show, Eq, Typeable, Data)

-- NFData instances for shouldNotTypecheck
instance NFData (Term a) where
  rnf (Variable x) = rnf x -- This is all we need to force the type error we're interested in
  rnf _ = ()

instance NFData (Var a) where
  rnf (Var s) = rnf s

instance NFData SubMap where
  rnf (SubMap m) = rnf m

#if __GLASGOW_HASKELL__ < 710
instance NFData TypeRep where
  rnf _ = ()
#endif

instance NFData Unifier where
  rnf (Unifier m) = rnf m

renameWithContext :: Renamer -> Int -> Term a -> Term a
renameWithContext renamer fresh t =
  let u = evalStateT (renameTerm t) renamer
  in evalState u fresh

renamePredWithContext :: Renamer -> Int -> Predicate -> Predicate
renamePredWithContext renamer fresh p =
  let u = evalStateT (renamePredicate p) renamer
  in evalState u fresh

renameGoalWithContext :: Renamer -> Int -> Goal -> Goal
renameGoalWithContext renamer fresh p =
  let u = evalStateT (renameGoal p) renamer
  in evalState u fresh

doRenameClause :: HornClause -> HornClause
doRenameClause c = runUnification $ renameClause c

test = describeModule "Control.Hspl.Internal.Unification" $ do
  describe "a unifier" $ do
    it "should have a singleton substitution operator" $
      toTerm True // Var "x" `shouldBe`
        Unifier (M.singleton (typeOf True) $ SubMap $ M.singleton (Var "x") (toTerm True))
    when "composed with another" $ do
      it "should result in the union of unifiers if the unifiers are disjoint" $ do
        (toTerm True // Var "x") <> (toTerm False // Var "y") `shouldBe`
          Unifier (M.singleton (typeOf True) $
            SubMap $ M.fromList [(Var "x", toTerm True), (Var "y", toTerm False)])
        (toTerm True // Var "x") <> (toTerm 'a' // Var "x") `shouldBe`
          Unifier (M.fromList [ (typeOf True, SubMap $ M.singleton (Var "x") (toTerm True))
                              , (typeOf 'a', SubMap $ M.singleton (Var "x") (toTerm 'a'))
                              ])
      it "should apply substitutions in the rhs to terms in the lhs" $ do
        (toTerm (Var "y" :: Var Bool) // Var "x") <> (toTerm True // Var "y") `shouldBe`
          Unifier (M.singleton (typeOf True) $
            SubMap $ M.fromList [(Var "x", toTerm True), (Var "y", toTerm True)])
        (toTerm (Var "y" :: Var Bool, 'a') // Var "x") <> (toTerm True // Var "y") `shouldBe`
          Unifier (M.fromList [ (typeOf True, SubMap $ M.singleton (Var "y") (toTerm True))
                              , (typeOf (True, 'a'), SubMap $ M.singleton (Var "x") (toTerm (True, 'a')))
                              ])
        (toTerm [toTerm $ Var "y", toTerm 'b'] // Var "x") <> (toTerm 'a' // Var "y") `shouldBe`
          Unifier (M.fromList [ (typeOf ['a'], SubMap $ M.singleton (Var "x") (toTerm ['a', 'b']))
                              , (typeOf 'a', SubMap $ M.singleton (Var "y") (toTerm 'a'))
                              ])
        (Constructor Just (toTerm (Var "y" :: Var Char)) // Var "x") <> (toTerm 'a' // Var "y") `shouldBe`
          Unifier (M.fromList [ (typeOf $ Just 'a', SubMap $ M.singleton (Var "x") (Constructor Just $ toTerm 'a'))
                              , (typeOf 'a', SubMap $ M.singleton (Var "y") (toTerm 'a'))
                              ])
      it "should prefer the lhs when the same variable appears on both sides" $
        (toTerm True // Var "x") <> (toTerm False // Var "x") `shouldBe`
          toTerm True // Var "x"
    when "empty" $ do
      it "should act as an identity of composition" $ do
        let u = toTerm True // Var "x"
        u <> mempty `shouldBe` u
        mempty <> u `shouldBe` u
      it "should act as an identity of unification" $ do
        let t = toTerm (Var "x" :: Var Bool)
        unifyTerm mempty t `shouldBe` t
    it "should not allow terms to replace variables of a different type" $ do
      -- This should work
      evaluate $ toTerm True // (Var "x" :: Var Bool)
      -- But this should not
      shouldNotTypecheck $ toTerm True // (Var "x" :: Var Char)
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
    when "querying variables" $ do
      it "should match variables by type first" $ do
        let u = (toTerm True // Var "x") <> (toTerm 'a' // Var "x")
        findVar u (Var "x" :: Var Bool) `shouldBe` Just (toTerm True)
        findVar u (Var "x" :: Var Char) `shouldBe` Just (toTerm 'a')
      it "should match variables of the same type by name" $ do
        let u = (toTerm True // Var "x") <> (toTerm False // Var "y")
        findVar u (Var "x") `shouldBe` Just (toTerm True)
        findVar u (Var "y") `shouldBe` Just (toTerm False)
      it "should allow the client to specify a default" $
        findVarWithDefault (toTerm True) mempty (Var "x") `shouldBe` toTerm True
      it "should return the unification status of a variable" $ do
        queryVar mempty (Var "x" :: Var Bool) `shouldBe` Ununified
        queryVar (toTerm 'a' // Var "x") (Var "x" :: Var Bool) `shouldBe` Ununified
        queryVar (toTerm True // Var "y") (Var "x" :: Var Bool) `shouldBe` Ununified
        queryVar (toTerm True // Var "x") (Var "x" :: Var Bool) `shouldBe` Unified True
        let t = Constructor Just (toTerm (Var "y" :: Var Bool))
        queryVar (t // Var "x") (Var "x" :: Var (Maybe Bool)) `shouldBe` Partial t
  describe "term unification" $ do
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
        mgu (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char)) `shouldBe` Just mempty
          -- ^ This should NOT fail the occurs check!
      it "should fail when the term being substituted contains the variable (occurs check)" $ do
        mgu (toTerm (Var "x" :: Var [Bool]))
            (List (toTerm True) (toTerm (Var "x" :: Var [Bool]))) `shouldBe` Nothing
        mgu (toTerm (Var "x" :: Var RecursiveType))
            (Constructor Rec (toTerm (Var "x" :: Var RecursiveType))) `shouldBe` Nothing
    when "both elements are constants" $ do
      it "should unify equal constants" $ do
        mgu (toTerm True) (toTerm True) `shouldBe` Just mempty
        mgu (toTerm 'a') (toTerm 'a') `shouldBe` Just mempty
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
        shouldNotTypecheck $ mgu (toTerm ('a', 'b')) (toTerm ('a', 'b', Var "x" :: Var Char))
    when "both terms are lists" $ do
      it "should unify the elements in sequence" $
        mgu (toTerm [toTerm 'a', toTerm (Var "x" :: Var Char)])
            (toTerm [toTerm (Var "y" :: Var Char), toTerm 'b']) `shouldBe`
          Just (toTerm 'a' // Var "y" <> toTerm 'b' // Var "x")
      it "should unify a variable with the tail of a list" $
        mgu (toTerm "abc") (List (toTerm 'a') (toTerm (Var "xs" :: Var String))) `shouldBe`
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
        mgu (Constructor Just (toTerm 'a')) (Constructor Just (toTerm $ Var "x")) `shouldBe`
          Just (toTerm 'a' // Var "x")
        mgu (Constructor Just (toTerm $ Var "x")) (Constructor Just (toTerm 'a')) `shouldBe`
          Just (toTerm 'a' // Var "x")
      it "should fail to unify terms with different constructors" $ do
        mgu (Constructor Left (toTerm 'a')) (Constructor Right (toTerm 'a')) `shouldBe` Nothing
        mgu (Constructor Left (toTerm 'a')) (Constructor Right (toTerm True)) `shouldBe` Nothing
        mgu (Constructor Left (toTerm (Var "x" :: Var Char)))
            (Constructor Right (toTerm (Var "y" :: Var Char))) `shouldBe`
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
      it "should fail to unify different types of expressions" $ do
        mgu (Sum (toTerm $ Var "x") (toTerm (1 :: Int)))
            (Difference (toTerm (2 :: Int)) (toTerm $ Var "y")) `shouldBe` Nothing
        mgu (Quotient (toTerm $ Var "x") (toTerm (1.0 :: Double)))
            (Product (toTerm $ Var "x") (toTerm (1.0 :: Double))) `shouldBe` Nothing
    it "should prohibit unification of terms of different types" $ do
      -- This should work
      evaluate $ mgu (toTerm True) (toTerm True)
      -- but not this
      shouldNotTypecheck $ mgu (toTerm True) (toTerm 'a')
  describe "term renaming" $ do
    let r = Renamer $ M.fromList [ (typeOf True, VarMap $ M.singleton (Var "x" :: Var Bool) (Fresh 0))
                                 , (typeOf 'a', VarMap $ M.fromList [ (Var "x" :: Var Char, Fresh 1)
                                                                    , (Var "y" :: Var Char, Fresh 2)
                                                                    , (Var "z" :: Var Char, Fresh 3)
                                                                    ])
                                 ]
    let rename = renameWithContext r 4
    context "of a variable" $ do
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
        let r = Renamer $ M.singleton (typeOf "foo") (VarMap $ M.singleton (Var "xs" :: Var String) (Fresh 0))
        renameWithContext r 1 (List (toTerm 'a') (toTerm $ Var "xs")) `shouldBe`
          List (toTerm 'a') (toTerm $ Fresh 0)
      it "should rename the same variable with the same replacement" $ do
        rename (toTerm [Var "x" :: Var Bool, Var "x" :: Var Bool]) `shouldBe`
          toTerm [Fresh 0 :: Var Bool, Fresh 0 :: Var Bool]
        rename (toTerm [Var "q" :: Var Char, Var "q" :: Var Char]) `shouldBe`
          toTerm [Fresh 4 :: Var Char, Fresh 4 :: Var Char]
    context "of an ADT constructor" $
      it "should recursively rename variables in the argument" $ do
        rename (Constructor Just (toTerm (Var "x" :: Var Char))) `shouldBe`
          Constructor Just (toTerm (Fresh 1 :: Var Char))
        rename (Constructor Just (toTerm (Var "x" :: Var Char, Var "q" :: Var Int))) `shouldBe`
          Constructor Just (toTerm (Fresh 1 :: Var Char, Fresh 4 :: Var Int))
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
  describe "predicate renaming" $ do
    let r = Renamer $ M.singleton (typeOf True) (VarMap $ M.singleton (Var "x" :: Var Bool) (Fresh 0))
    let rename = renamePredWithContext r 1
    it "should rename variables in the argument if the renamer applies" $
      rename (predicate "foo" (Var "x" :: Var Bool)) `shouldBe` predicate "foo" (Fresh 0 :: Var Bool)
    it "should create fresh variables when the argument contains a variable not in the renamer" $
      rename (predicate "foo" (Var "q" :: Var Bool)) `shouldBe` predicate "foo" (Fresh 1 ::Var Bool)
  describe "goal renaming" $ do
    let rename = renameGoalWithContext (Renamer M.empty) 0
    context "of predicate goals" $
      it "should rename variables in the predicate" $
        rename (PredGoal $ predicate "foo" (Var "x" :: Var Bool)) `shouldBe`
          PredGoal (predicate "foo" (Fresh 0 :: Var Bool))
    context "of CanUnify goals" $ do
      it "should rename variables in each term" $
        rename (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          CanUnify (toTerm (Fresh 0 :: Var Char)) (toTerm (Fresh 1 :: Var Char))
      it "should rename variables in both terms the same" $
        rename (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
          CanUnify (toTerm (Fresh 0 :: Var Char)) (toTerm (Fresh 0 :: Var Char))
    context "of Identical goals" $ do
      it "should rename variables in each term" $
        rename (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          Identical (toTerm (Fresh 0 :: Var Char)) (toTerm (Fresh 1 :: Var Char))
      it "should rename variables in both terms the same" $
        rename (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
          Identical (toTerm (Fresh 0 :: Var Char)) (toTerm (Fresh 0 :: Var Char))
    context "of Not goals" $
      it "should rename variables in the inner goal" $
        rename (Not $ PredGoal $ predicate "foo" (Var "x" :: Var Bool)) `shouldBe`
          Not (PredGoal $ predicate "foo" (Fresh 0 :: Var Bool))
    context "of Equal goals" $ do
      it "should rename variables in each term" $
        rename (Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))) `shouldBe`
          Equal (toTerm (Fresh 0 :: Var Int)) (toTerm (Fresh 1 :: Var Int))
      it "should rename variables in both terms the same" $
        rename (Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "x" :: Var Int))) `shouldBe`
          Equal (toTerm (Fresh 0 :: Var Int)) (toTerm (Fresh 0 :: Var Int))
  describe "clause renaming" $ do
    let rename = doRenameClause
    it "should rename variables in the positive literal" $
      rename (HornClause (predicate "foo" (Var "x" :: Var Bool)) []) `shouldBe`
        HornClause (predicate "foo" (Fresh 0 :: Var Bool)) []
    it "should rename variables in all negative literals" $ do
      rename (HornClause ( predicate "foo" ())
                         [ PredGoal $ predicate "bar" (Var "x" :: Var Bool)
                         , PredGoal $ predicate "baz" (Var "x" :: Var Bool)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ PredGoal $ predicate "bar" (Fresh 0 :: Var Bool)
                   , PredGoal $ predicate "baz" (Fresh 0 :: Var Bool)]
      rename (HornClause ( predicate "foo" ())
                         [ PredGoal $ predicate "bar" (Var "x" :: Var Bool)
                         , PredGoal $ predicate "baz" (Var "q" :: Var Char)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ PredGoal $ predicate "bar" (Fresh 0 :: Var Bool)
                   , PredGoal $ predicate "baz" (Fresh 1 :: Var Char)]
    it "should apply renamings generated in the positive literal to the negative literals" $
      rename (HornClause (predicate "foo" (Var "q" :: Var Char, Var "p" :: Var Char))
                         [PredGoal $ predicate "bar" (Var "p" :: Var Char)]) `shouldBe`
        HornClause (predicate "foo" (Fresh 0 :: Var Char, Fresh 1 :: Var Char))
                   [PredGoal $ predicate "bar" (Fresh 1 :: Var Char)]
    it "should apply renamings generated in a negative literal to all subsequent negative literals" $
      rename (HornClause ( predicate "foo" ())
                         [ PredGoal $ predicate "bar" (Var "q" :: Var Char, Var "p" :: Var Char)
                         , PredGoal $ predicate "baz" (Var "p" :: Var Char)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ PredGoal $ predicate "bar" (Fresh 0 :: Var Char, Fresh 1 :: Var Char)
                   , PredGoal $ predicate "baz" (Fresh 1 :: Var Char)]
  describe "term unifier application" $ do
    context "to a variable" $ do
      it "should replace the variable if there is a corresponding substitution" $
        unifyTerm (toTerm 'a' // Var "x") (toTerm (Var "x" :: Var Char)) `shouldBe` toTerm 'a'
      it "should return the original variable if there is no substitution" $ do
        let x = toTerm (Var "x" :: Var Char)
        unifyTerm mempty x `shouldBe` x
        unifyTerm (toTerm 'a' // Var "y") x `shouldBe` x -- No substitution for the right name
        unifyTerm (toTerm True // Var "x") x `shouldBe` x -- No substitution for the right type
    context "to a constant" $
      it "should return the original constant" $ do
        let u = toTerm 'a' // Var "x" <> toTerm True // Var "y"
        unifyTerm u (toTerm 'z') `shouldBe` toTerm 'z'
        unifyTerm u (toTerm False) `shouldBe` toTerm False
    context "to a tuple" $
      it "should recursively apply the unifier to each element" $ do
        unifyTerm (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (toTerm ("foo", Var "y" :: Var Bool, Var "x" :: Var Bool, Var "x" :: Var Char)) `shouldBe`
          toTerm ("foo", True, Var "x" :: Var Bool, 'a')
        unifyTerm (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (toTerm (Var "x" :: Var Char, ('z', Var "y" :: Var Bool))) `shouldBe`
          toTerm ('a', ('z', True))
    context "to a list" $ do
      it "should recursively apply the unifier to each element" $
        unifyTerm (toTerm 'a' // Var "x")
                  (toTerm [toTerm $ Var "x", toTerm 'b', toTerm $ Var "y"]) `shouldBe`
          toTerm [toTerm 'a', toTerm 'b', toTerm $ Var "y"]
      it "should apply the unifier to the tail of a list" $
        unifyTerm (toTerm "xyz" // Var "xs")
                  (List (toTerm (Var "x" :: Var Char)) (toTerm $ Var "xs")) `shouldBe`
          toTerm [toTerm $ Var "x", toTerm 'x', toTerm 'y', toTerm 'z']
    context "to an ADT constructor" $
      it "should recursively apply the unifier to the argument" $
        unifyTerm (toTerm 'a' // Var "x") (Constructor Just $ toTerm (Var "x" :: Var Char)) `shouldBe`
          Constructor Just (toTerm 'a')
    context "to an arithmetic expression" $
      it "should recursively apply the unifier to each element" $ do
        unifyTerm (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Sum (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Sum (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unifyTerm (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Difference (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Difference (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unifyTerm (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (Product (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          Product (toTerm (1 :: Int)) (toTerm (2 :: Int))
        unifyTerm (toTerm (1.0 :: Double) // Var "x" <> (2.0 :: Double) // Var "y")
                  (Quotient (toTerm (Var "x" :: Var Double)) (toTerm $ Var "y")) `shouldBe`
          Quotient (toTerm (1.0 :: Double)) (toTerm (2.0 :: Double))
        unifyTerm (toTerm (1 :: Int) // Var "x" <> (2 :: Int) // Var "y")
                  (IntQuotient (toTerm (Var "x" :: Var Int)) (toTerm $ Var "y")) `shouldBe`
          IntQuotient (toTerm (1 :: Int)) (toTerm (2 :: Int))
  describe "predicate unifier application" $ do
    it "should unify the argument when the unifier applies" $
      unifyPredicate (toTerm 'a' // Var "x") (predicate "foo" (Var "x" :: Var Char)) `shouldBe`
        predicate "foo" 'a'
    it "should return the original predicate when the unifier is irrelevant" $ do
      let p = predicate "foo" (Var "x" :: Var Char)
      unifyPredicate mempty p `shouldBe` p
      unifyPredicate (toTerm 'a' // Var "y") p `shouldBe` p
      unifyPredicate (toTerm True // Var "x") p `shouldBe` p
  describe "goal unifier application" $ do
    context "to a predicate goal" $
      it "should unify the predicate" $
        unifyGoal (toTerm 'a' // Var "x") (PredGoal $ predicate "foo" (Var "x" :: Var Char)) `shouldBe`
          PredGoal (predicate "foo" 'a')
    context "to a CanUnify goal" $ do
      it "should unify both terms" $
        unifyGoal (toTerm 'a' // Var "x" <> toTerm 'b' // Var "y")
          (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          CanUnify (toTerm 'a') (toTerm 'b')
      it "should leave either term unchanged when the unifier does not apply" $ do
        let u = toTerm 'a' // Var "x"
        unifyGoal u (CanUnify (toTerm (Var "y" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
          CanUnify (toTerm (Var "y" :: Var Char)) (toTerm 'a')
        unifyGoal u (CanUnify (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          CanUnify (toTerm 'a') (toTerm (Var "y" :: Var Char))
    context "to an Identical goal" $ do
      it "should unify both terms" $
        unifyGoal (toTerm 'a' // Var "x" <> toTerm 'b' // Var "y")
          (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          Identical (toTerm 'a') (toTerm 'b')
      it "should leave either term unchanged when the unifier does not apply" $ do
        let u = toTerm 'a' // Var "x"
        unifyGoal u (Identical (toTerm (Var "y" :: Var Char)) (toTerm (Var "x" :: Var Char))) `shouldBe`
          Identical (toTerm (Var "y" :: Var Char)) (toTerm 'a')
        unifyGoal u (Identical (toTerm (Var "x" :: Var Char)) (toTerm (Var "y" :: Var Char))) `shouldBe`
          Identical (toTerm 'a') (toTerm (Var "y" :: Var Char))
    context "to a Not goal" $
      it "should unify the inner goal" $
        unifyGoal (toTerm 'a' // Var "x")
                  (Not $ PredGoal $ predicate "foo" (Var "x" :: Var Char)) `shouldBe`
          Not (PredGoal $ predicate "foo" 'a')
    context "to an Equal goal" $ do
      it "should unify both terms" $
        unifyGoal (toTerm (1 :: Int) // Var "x" <> toTerm (2 :: Int) // Var "y")
          (Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))) `shouldBe`
          Equal (toTerm (1 :: Int)) (toTerm (2 :: Int))
      it "should leave either term unchanged when the unifier does not apply" $ do
        let u = toTerm (1 :: Int) // Var "x"
        unifyGoal u (Equal (toTerm (Var "y" :: Var Int)) (toTerm (Var "x" :: Var Int))) `shouldBe`
          Equal (toTerm (Var "y" :: Var Int)) (toTerm (1 :: Int))
        unifyGoal u (Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))) `shouldBe`
          Equal (toTerm (1 :: Int)) (toTerm (Var "y" :: Var Int))
  describe "clause unifier application" $ do
    it "should unify the positive literal when the unifier applies" $
      unifyClause (toTerm 'a' // Var "x")
                  (HornClause (predicate "foo" (Var "x" :: Var Char)) []) `shouldBe`
        HornClause (predicate "foo" 'a') []
    it "should unify the negative literals when the unifier applies" $
      unifyClause (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (HornClause (predicate "foo" ())
                              [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                              , CanUnify (toTerm (Var "y" :: Var Bool)) (toTerm False)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ PredGoal $ predicate "bar" 'a'
                   , CanUnify (toTerm True) (toTerm False)]
    it "should leave the positive literal unchanged when the unifier does not apply" $ do
      let c = HornClause (predicate "foo" (Var "x" :: Var Char)) []
      unifyClause mempty c `shouldBe` c
      unifyClause (toTerm 'a' // Var "y") c `shouldBe` c
      unifyClause (toTerm True // Var "x") c `shouldBe` c
    it "should leave any of the negative literals unchanged when the unifier does not apply" $ do
      let c = HornClause ( predicate "foo" ())
                         [ PredGoal $ predicate "bar" (Var "x" :: Var Bool)
                         , PredGoal $ predicate "baz" (Var "y" :: Var Char)
                         , CanUnify (toTerm True) (toTerm (Var "q" :: Var Bool))]
      unifyClause mempty c `shouldBe` c
      unifyClause (toTerm True // Var "x") c `shouldBe`
        HornClause ( predicate "foo" ())
                   [ PredGoal $ predicate "bar" True
                   , PredGoal $ predicate "baz" (Var "y" :: Var Char)
                   , CanUnify (toTerm True) (toTerm (Var "q" :: Var Bool))]
      unifyClause (toTerm 'a' // Var "y") c `shouldBe`
        HornClause ( predicate "foo" ())
                   [ PredGoal $ predicate "bar" (Var "x" :: Var Bool)
                   , PredGoal $ predicate "baz" 'a'
                   , CanUnify (toTerm True) (toTerm (Var "q" :: Var Bool))]
      unifyClause (toTerm True // Var "z") c `shouldBe` c
  describe "full unification" $ do
    let runTest p c = runUnification (unify p c)
    it "should rename variables in the clause" $
      runTest (predicate "foo" ())
            (HornClause ( predicate "foo" ())
                        [ PredGoal $ predicate "bar" (Var "x" :: Var Bool)
                        , CanUnify (toTerm 'a') (toTerm (Var "y" :: Var Char))]) `shouldBe`
        Just ([ PredGoal $ predicate "bar" (Fresh 0 :: Var Bool)
              , CanUnify (toTerm 'a') (toTerm (Fresh 1 :: Var Char))], mempty)
    it "should return any unifications made" $
      runTest (predicate "foo" ('a', Var "x" :: Var Bool))
            (HornClause (predicate "foo" (Var "y" :: Var Char, True)) []) `shouldBe`
        Just ([], toTerm 'a' // Fresh 0 <> toTerm True // Var "x")
    it "should apply the unifier to variables in the clause" $
      runTest (predicate "foo" 'a')
            (HornClause ( predicate "foo" (Var "x" :: Var Char))
                        [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                        , CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char))]) `shouldBe`
        Just ([ PredGoal $ predicate "bar" 'a'
              , CanUnify (toTerm 'a') (toTerm 'a')], toTerm 'a' // Fresh 0)
    it "should not apply the unifier to renamed variables" $
      runTest (predicate "foo" (Var "x" :: Var Char))
            (HornClause ( predicate "foo" 'a')
                        [ PredGoal $ predicate "bar" (Var "x" :: Var Char)
                        , CanUnify (toTerm 'a') (toTerm (Var "x" :: Var Char))]) `shouldBe`
        Just ([ PredGoal $ predicate "bar" (Fresh 0 :: Var Char)
              , CanUnify (toTerm 'a') (toTerm (Fresh 0 :: Var Char))], toTerm 'a' // Var "x")
    it "should fail when the goal does not unify with the clause" $
      runTest (predicate "foo" 'a') (HornClause (predicate "foo" 'b') []) `shouldBe` Nothing
