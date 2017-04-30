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
import           Data.Monoid
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

renameClauseWithContext :: Int -> HornClause -> HornClause
renameClauseWithContext fresh c = evalState (renameClause c) fresh

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
  describe "predicate renaming" $ do
    let r = Renamer $ M.singleton (typeOf True) (VarMap $ M.singleton (Var "x" :: Var Bool) (Fresh 0))
    let rename = renamePredWithContext r 1
    it "should rename variables in the argument if the renamer applies" $
      rename (predicate "foo" (Var "x" :: Var Bool)) `shouldBe` predicate "foo" (Fresh 0 :: Var Bool)
    it "should create fresh variables when the argument contains a variable not in the renamer" $
      rename (predicate "foo" (Var "q" :: Var Bool)) `shouldBe` predicate "foo" (Fresh 1 ::Var Bool)
  describe "clause renaming" $ do
    let rename = renameClauseWithContext 0
    it "should rename variables in the positive literal" $
      rename (HornClause (predicate "foo" (Var "x" :: Var Bool)) []) `shouldBe`
        HornClause (predicate "foo" (Fresh 0 :: Var Bool)) []
    it "should rename variables in all negative literals" $ do
      rename (HornClause ( predicate "foo" ())
                         [ predicate "bar" (Var "x" :: Var Bool)
                         , predicate "baz" (Var "x" :: Var Bool)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ predicate "bar" (Fresh 0 :: Var Bool)
                   , predicate "baz" (Fresh 0 :: Var Bool)]
      rename (HornClause ( predicate "foo" ())
                         [ predicate "bar" (Var "x" :: Var Bool)
                         , predicate "baz" (Var "q" :: Var Char)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ predicate "bar" (Fresh 0 :: Var Bool)
                   , predicate "baz" (Fresh 1 :: Var Char)]
    it "should apply renamings generated in the positive literal to the negative literals" $
      rename (HornClause (predicate "foo" (Var "q" :: Var Char, Var "p" :: Var Char))
                         [predicate "bar" (Var "p" :: Var Char)]) `shouldBe`
        HornClause (predicate "foo" (Fresh 0 :: Var Char, Fresh 1 :: Var Char))
                   [predicate "bar" (Fresh 1 :: Var Char)]
    it "should apply renamings generated in a negative literal to all subsequent negative literals" $
      rename (HornClause ( predicate "foo" ())
                         [ predicate "bar" (Var "q" :: Var Char, Var "p" :: Var Char)
                         , predicate "baz" (Var "p" :: Var Char)]) `shouldBe`
        HornClause ( predicate "foo" ())
                   [ predicate "bar" (Fresh 0 :: Var Char, Fresh 1 :: Var Char)
                   , predicate "baz" (Fresh 1 :: Var Char)]
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
  describe "predicate unifier application" $ do
    it "should unify the argument when the unifier applies" $
      unifyPredicate (toTerm 'a' // Var "x") (predicate "foo" (Var "x" :: Var Char)) `shouldBe`
        predicate "foo" 'a'
    it "should return the original predicate when the unifier is irrelevant" $ do
      let p = predicate "foo" (Var "x" :: Var Char)
      unifyPredicate mempty p `shouldBe` p
      unifyPredicate (toTerm 'a' // Var "y") p `shouldBe` p
      unifyPredicate (toTerm True // Var "x") p `shouldBe` p
  describe "clause unifier application" $ do
    it "should unify the positive literal when the unifier applies" $
      unifyClause (toTerm 'a' // Var "x")
                  (HornClause (predicate "foo" (Var "x" :: Var Char)) []) `shouldBe`
        HornClause (predicate "foo" 'a') []
    it "should unify the negative literals when the unifier applies" $
      unifyClause (toTerm 'a' // Var "x" <> toTerm True // Var "y")
                  (HornClause (predicate "foo" ())
                              [ predicate "bar" (Var "x" :: Var Char)
                              , predicate "baz" (Var "y" :: Var Bool)]) `shouldBe`
        HornClause (predicate "foo" ()) [predicate "bar" 'a', predicate "baz" True]
    it "should leave the positive literal unchanged when the unifier does not apply" $ do
      let c = HornClause (predicate "foo" (Var "x" :: Var Char)) []
      unifyClause mempty c `shouldBe` c
      unifyClause (toTerm 'a' // Var "y") c `shouldBe` c
      unifyClause (toTerm True // Var "x") c `shouldBe` c
    it "should leave any of the negative literals unchanged when the unifier does not apply" $ do
      let c = HornClause ( predicate "foo" ())
                         [ predicate "bar" (Var "x" :: Var Bool)
                         , predicate "baz" (Var "y" :: Var Char)]
      unifyClause mempty c `shouldBe` c
      unifyClause (toTerm True // Var "x") c `shouldBe`
        HornClause (predicate "foo" ()) [predicate "bar" True, predicate "baz" (Var "y" :: Var Char)]
      unifyClause (toTerm 'a' // Var "y") c `shouldBe`
        HornClause (predicate "foo" ()) [predicate "bar" (Var "x" :: Var Bool), predicate "baz" 'a']
      unifyClause (toTerm True // Var "z") c `shouldBe` c
  describe "goal unification" $ do
    let unify p c = evalState (unifyGoal p c) 0
    it "should rename variables in the clause" $
      unify (predicate "foo" ())
            (HornClause (predicate "foo" ()) [predicate "bar" (Var "x" :: Var Bool)]) `shouldBe`
        Just [predicate "bar" (Fresh 0 :: Var Bool)]
    it "should apply the unifier to variables in the clause" $
      unify (predicate "foo" 'a')
            (HornClause (predicate "foo" (Var "x" :: Var Char))
                        [predicate "bar" (Var "x" :: Var Char)]) `shouldBe`
        Just [predicate "bar" 'a']
    it "should not apply the unifier to renamed variables" $
      unify (predicate "foo" (Var "x" :: Var Char))
            (HornClause (predicate "foo" 'a')
                        [predicate "bar" (Var "x" :: Var Char)]) `shouldBe`
        Just [predicate "bar" (Fresh 0 :: Var Char)]
    it "should fail when the goal does not unify with the clause" $
      unify (predicate "foo" 'a') (HornClause (predicate "foo" 'b') []) `shouldBe` Nothing
