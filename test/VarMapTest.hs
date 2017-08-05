module VarMapTest where

import Testing
import Control.Hspl.Internal.VarMap (VarMap (..), SubMap (..), Entry (..))
import qualified Control.Hspl.Internal.VarMap as VM

import Control.Hspl.Internal.Ast

import Control.Monad.Writer
import qualified Data.Map as M
import Data.Typeable

example1 = VM.insert (Var "x") (toTerm 'a') VM.empty
example2 = VM.insert (Var "y") (toTerm 'b') example1
example3 = VM.insert (Var "x") (toTerm True) example2
mapLists = [ (VM.empty, [])
           , (example1, [Entry (Var "x") (toTerm 'a')])
           , (example2, [Entry (Var "x") (toTerm 'a'), Entry (Var "y") (toTerm 'b')])
           , (example3, [ Entry (Var "x") (toTerm 'a')
                        , Entry (Var "y") (toTerm 'b')
                        , Entry (Var "x") (toTerm True)
                        ])
           ]

test = describeModule "Control.Hspl.Internal.VarMap" $ do
  describe "empty" $
    it "should create an empty outer map" $ do
      (VM.empty :: VarMap Var) `shouldBe` VarMap M.empty
      (VM.empty :: VarMap Term) `shouldBe` VarMap M.empty

  describe "singleton" $
    it "should create a VarMap containing a single mapping" $ do
      VM.singleton (Var "x") (toTerm 'a') `shouldBe`
        VarMap (M.singleton (typeOf 'a') $ SubMap $ M.singleton (Var "x") (toTerm 'a'))
      VM.singleton (Var "x" :: Var Char) (Var "y") `shouldBe`
        VarMap (M.singleton (typeOf 'a') $ SubMap $ M.singleton (Var "x" :: Var Char) (Var "y"))

  describe "insert" $ do
    it "should create and insert a new SubMap" $ do
      let m = VM.insert (Var "x") (toTerm True) VM.empty
      m `shouldBe` VarMap (M.singleton (typeOf True) $ SubMap $ M.singleton (Var "x") (toTerm True))

      let m' = VM.insert (Var "x") (toTerm 'a') m
      m' `shouldBe` VarMap (M.fromList [ (typeOf True, SubMap $ M.singleton (Var "x") (toTerm True))
                                       , (typeOf 'a', SubMap $ M.singleton (Var "x") (toTerm 'a'))
                                       ])
    it "should insert into an existing SubMap" $ do
      let m = VM.insert (Var "x") (toTerm True) VM.empty
      VM.insert (Var "y") (toTerm False) m `shouldBe`
        VarMap (M.singleton (typeOf True) $ SubMap $ M.fromList [ (Var "x", toTerm True)
                                                                , (Var "y", toTerm False)
                                                                ])
    it "should update an existing SubMap" $ do
      let m = VM.insert (Var "x") (toTerm True) VM.empty
      VM.insert (Var "x") (toTerm False) m `shouldBe`
        VarMap (M.singleton (typeOf True) $ SubMap $ M.singleton (Var "x") (toTerm False))

  describe "fromList, toList, and collect" $
    withParams mapLists $ \(m, l) -> do
      it "should insert each mapping in a list of Entries" $
        VM.fromList l `shouldBe` m
      it "should turn a VarMap into a list of Entries" $
        VM.toList m `shouldBePermutationOf` l
      it "should apply a function to each mapping in a VarMap" $
        VM.collect Entry m `shouldBePermutationOf` l

  describe "lookup" $ do
    let m1 = VM.insert (Var "x" :: Var Char) (Fresh 0) VM.empty
    let m2 = VM.insert (Var "y" :: Var Char) (Fresh 1) m1
    let m3 = VM.insert (Var "z" :: Var Bool) (Fresh 2) m2
    withParams [m1, m2, m3] $ \m ->
      it "should find a key in the map" $
        VM.lookup (Var "x" :: Var Char) m `shouldBe` Just (Fresh 0)
    withParams [VM.empty, m1, m2] $ \m ->
      it "should not find a key when the corresponding SubMap does not exist" $
        VM.lookup (Var "z" :: Var Bool) m `shouldBe` Nothing
    withParams [m1, m2, m3] $ \m ->
      it "should not find a key which is not present in the corresponding SubMap" $
        VM.lookup (Var "z" :: Var Char) m `shouldBe` Nothing

  describe "findWithDefault" $ do
    it "should return the value from the VarMap when found" $
      VM.findWithDefault (toTerm 'a') (Var "x") (VM.fromList [Entry (Var "x") (toTerm 'b')])
        `shouldBe` toTerm 'b'
    it "should return the default value when the key is not found" $
      VM.findWithDefault (toTerm 'a') (Var "x") VM.empty `shouldBe` toTerm 'a'

  describe "containsKey" $ do
    it "should return True when given a key contained in the VarMap" $
      VM.fromList [Entry (Var "x") (toTerm 'a')] `shouldSatisfy`
        VM.containsKey (Var "x" :: Var Char)
    it "should return False when given a key not contained in the VarMap" $
      VM.fromList [Entry (Var "x") (toTerm 'a')] `shouldSatisfy`
        not . VM.containsKey (Var "y" :: Var Char)

  describe "containsMapping" $ do
    it "should return True when given a mapping contained in the VarMap" $
      VM.fromList [Entry (Var "x") (toTerm 'a')] `shouldSatisfy`
        VM.containsMapping (Var "x") (toTerm 'a')
    it "should return False when given a key not contained in the VarMap" $
      VM.fromList [Entry (Var "x") (toTerm 'a')] `shouldSatisfy`
        not. VM.containsMapping (Var "y") (toTerm 'a')
    it "should return False when given a key which maps to a different value" $
      VM.fromList [Entry (Var "x") (toTerm 'a')] `shouldSatisfy`
        not . VM.containsMapping (Var "x") (toTerm 'b')

  describe "map" $
    withParams mapLists $ \(m, l) ->
      it "should transform every value" $ do
        let f :: TermEntry a => Term a -> Term a
            f = Variable . Var . show
        let mapEntry :: Entry Term -> Entry Term
            mapEntry (Entry k v) = Entry k $ f v
        VM.map f m `shouldBe` VM.fromList (map mapEntry l)

  describe "monadic looping" $
    withParams mapLists $ \(m, l) ->
      it "should execute an action for each mapping in a VarMap" $ do
        let results :: ([()], [Entry Term])
            results = runWriter (VM.for m $ \k v -> tell [Entry k v])
            (units, entries) = results
        units `shouldBe` [() | _ <- l]
        entries `shouldBePermutationOf` l

        let (unit, entries) = runWriter (VM.for_ m $ \k v -> tell [Entry k v])
        unit `shouldBe` ()
        entries `shouldBePermutationOf` l

  describe "the VarMap monoid instance" $ do
    it "should have mempty == empty" $
      mempty `shouldBe` (VM.empty :: VarMap Var)
    it "should append by inserting each element from the left map into the right map" $ do
      mappend (VM.fromList [Entry (Var "x") (toTerm 'a')])
              (VM.fromList [Entry (Var "y") (toTerm 'b')])
        `shouldBe` VM.fromList [Entry (Var "x") (toTerm 'a'), Entry (Var "y") (toTerm 'b')]

      mappend (VM.fromList [Entry (Var "x") (toTerm 'a')])
              (VM.fromList [Entry (Var "y") (toTerm True)])
        `shouldBe` VM.fromList [Entry (Var "x") (toTerm 'a'), Entry (Var "y") (toTerm True)]

      mappend (VM.fromList [Entry (Var "x") (toTerm 'a')])
              (VM.fromList [Entry (Var "x") (toTerm 'b')])
        `shouldBe` VM.fromList [Entry (Var "x") (toTerm 'a')]

      mappend (VM.fromList [Entry (Var "x") (toTerm 'a'), Entry (Var "y") (toTerm True)])
              (VM.fromList [Entry (Var "w") (toTerm 'b'), Entry (Var "z") (toTerm False)])
        `shouldBe` VM.fromList [ Entry (Var "x") (toTerm 'a')
                               , Entry (Var "y") (toTerm True)
                               , Entry (Var "w") (toTerm 'b')
                               , Entry (Var "z") (toTerm False)
                               ]
