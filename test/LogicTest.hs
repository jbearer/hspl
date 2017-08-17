{-# LANGUAGE TupleSections #-}

module LogicTest where

import Testing
import Control.Hspl.Internal.Logic

import Control.Applicative
import Data.Maybe

runTest :: (Show a, Eq a, Show bs, Eq bs, Show gs, Eq gs) =>
           Logic bs gs a -> bs -> gs -> ([(a, bs)], gs) -> Expectation
runTest m bs gs (expectedBacktracking, expectedGs) =
  let (expected, expectedBs) = unzip expectedBacktracking
  in do
    observeAllLogic m bs gs `shouldBe` expected
    execAllLogic m bs gs `shouldBe` (expectedBs, expectedGs)
    runAllLogic m bs gs `shouldBe` (expectedBacktracking, expectedGs)

test = describeModule "Control.Hspl.Internal.Logic" $ do
  withParams [(<|>), mplus] $ \op ->
    describe "(<|>) or mplus" $ do
      it "should yield multiple results" $
        runTest (return 'a' `op` return 'b') 'x' 'y'
          ([('a', 'x'), ('b', 'x')], 'y')
      it "should backtrack the backtracking state" $
        runTest ((putBacktracking 's' >> getBacktracking) `op` getBacktracking) 'x' 'y'
          ([('s', 's'), ('x', 'x')], 'y')
      it "should not backtrack the global state" $
        runTest ((putGlobal 's' >> getGlobal) `op` getGlobal) 'x' 'y'
          ([('s', 'x'), ('s', 'x')], 's')

  describe "binding" $ do
    it "should apply a function to each current result" $
      runTest ((return 'a' <|> return 'b') >>= (return . (:"z")) :: Logic () () String) () ()
        ([("az", ()), ("bz", ())], ())
    it "should thread backtracking state" $ do
      runTest ((putBacktracking 'a' <|> putBacktracking 'b') >>= const getBacktracking) 'z' ()
        ([('a', 'a'), ('b', 'b')], ())
      runTest (putBacktracking 'a' >>= const (return 'b' <|> getBacktracking)) 'z' ()
        ([('b', 'a'), ('a', 'a')], ())
    it "should thread global state" $ do
      runTest ((modifyGlobal (+1) <|> modifyGlobal (+2)) >>= const (getGlobal <* modifyGlobal (+1))) () 0
        ([(1 :: Int, ()), (4, ())], 5 :: Int)
      runTest (putGlobal 'a' >>= const (return 'b' <|> getGlobal)) () 'z'
        ([('b', ()), ('a', ())], 'a')

  describe "cut" $ do
    it "should discard all choice points in the topmost frame" $ do
      runTest (return 'a' <|> commit 'b' <|> return 'c') () ()
        ([('a', ()), ('b', ())], ())
      runTest ((return 'a' <|> return 'b') >>= \c -> commit [c, 'y'] <|> return [c, 'z']) () ()
        ([("ay", ())], ())
    it "should discard all choice points in the current frame" $ do
      runTest (cutFrame (commit 'a' <|> return 'b') <|> return 'c') ()
        [('a', ()), ('c', ())]
      runTest (cutFrame ((return 'a' <|> return 'b') >>= \c -> commit [c, 'y'] <|> return [c, 'z']) <|> return "foo") ()
        [("ay", ()), ("foo", ())]
    it "should prevent side-effects in the unexplored branch" $
      tempFile $ \f -> do
        let m = cut <|> liftIO (writeFile f "hello")
        observeAllLogicT m ()
        output <- readFile f
        output `shouldSatisfy` null
    it "should bubble through msplit" $ do
      let m = (msplit (commit 'a') <|> return (Just ('b', mzero))) >>= maybe mzero (return . fst)
      runTest m () [('a', ())]

  withParams [fail "foo", mzero, empty] $ \op ->
    describe "fail/mzero/empty" $ do
      it "should abort the current branch and backtrack" $ do
        runTest (return 'a' <|> op <|> return 'c') 'x' 'y'
          ([('a', 'x'), ('c', 'x')], 'y')
        runTest ((return 'a' <|> return 'b') >>= \c -> op <|> return c) 'x' 'y'
          ([('a', 'x'), ('b', 'x')], 'y')
      it "should persist modifications to global state" $
        runTest (putGlobal 'z' >> op <|> return 'a') 'x' 'y'
          ([('a', 'x')], 'z')
      it "should not persist modifications to backtracking state" $
        runTest ((putBacktracking 'z' >> op) <|> getBacktracking) 'x' 'y'
          ([('x', 'x')], 'y')

  describe "runMany" $ do
    withParams [[], ['a'], ['a', 'b']] $ \results ->
      it "should return all results when there are at most the expected number" $ do
        let m = msum $ map return results
        runManyLogic 2 m 's' 't' `shouldBe` (map (,'s') results, 't')
        execManyLogic 2 m 's' 't' `shouldBe` (map (const 's') results, 't')
        observeManyLogic 2 m 's' 't' `shouldBe` results
    withParams ["abc", "abcd"] $ \results ->
      it "should return at most the requested number of results" $ do
        let m = msum $ map return results
        runManyLogic 2 m 's' 't' `shouldBe` (map (,'s') $ take 2 results, 't')
        execManyLogic 2 m 's' 't' `shouldBe` ("ss", 't')
        observeManyLogic 2 m 's' 't' `shouldBe` take 2 results
    withParams [-1, 0] $ \count ->
      it "should return an empty list when zero or fewer results are requested" $ do
        runManyLogic count (return 'a') 's' 't' `shouldBe` ([], 't')
        execManyLogic count (return 'a') 's' 't' `shouldBe` ([], 't')
        observeManyLogic count (return 'a') 's' 't' `shouldBe` []
    it "should properly thread backtracking state" $
      runManyLogic 2 (putBacktracking 'a' >> (return 'b' <|> getBacktracking)) 's' 't' `shouldBe`
        ([('b', 'a'), ('a', 'a')], 't')
    it "should properly thread global state" $ do
      runManyLogic 2 (putGlobal 'a' >> (return 'b' <|> getGlobal)) 's' 't' `shouldBe`
        ([('b', 's'), ('a', 's')], 'a')
      runManyLogic 2 ((putGlobal 'a' >> return 'b') <|> getGlobal) 's' 't' `shouldBe`
        ([('b', 's'), ('a', 's')], 'a')
    it "should maintain the cut stack between alternatives" $
      observeManyLogic 4 (cutFrame (return 'a' <|> commit 'b' <|> return 'c') <|> return 'd') () ()
        `shouldBe` "abd"

  describe "msplit" $ do
    it "should return the first result of a nondeterministic computation" $ do
      let results = observeAllLogic (msplit $ return 'a' <|> return 'b') () ()
      length results `shouldBe` 1
      guard $ isJust $ head results
      fst (fromJust $ head results) `shouldBe` 'a'
    it "should return Nothing when there are no results" $ do
      let results = observeAllLogic (msplit mzero) () ()
      length results `shouldBe` 1
      guard (isNothing $ head results)
    it "should return a suspension which yields the rest of the results" $ do
      let results = observeAllLogic (msplit $ return 'a' <|> return 'b') () ()
      length results `shouldBe` 1
      guard $ isJust $ head results
      let m = snd $ fromJust $ head results
      runTest m () ()
        ([('b', ())], ())
    it "should preserve global state" $
      runTest (putGlobal 'a' >> msplit (return 'z') >>=
               \m -> liftM2 (,) getGlobal (return $ fst $ fromJust m)) 's' 't'
        ([(('a', 'z'), 's')], 'a')
    it "should preserve backtracking state" $
      runTest ((putBacktracking 'a' <|> putBacktracking 'b') >> msplit (return 'z') >>=
               \m -> liftM2 (,) getBacktracking (return $ fst $ fromJust m)) 's' 't'
        ([(('a', 'z'), 'a'), (('b', 'z'), 'b')], 't')
    it "should preserve the cut stack" $
      runTest (cutFrame (msplit (return 'a' <|> return 'b') >>= commit . fst . fromJust) <|> return 'c') () ()
        ([('a', ()), ('c', ())], ())
    it "should preserve the cut stack in the suspension" $ do
      let results = observeAllLogic (msplit $ cutFrame (return 'a' <|> commit 'b' <|> return 'c') <|> return 'd') () ()
      length results `shouldBe` 1
      guard $ isJust $ head results
      let m = snd $ fromJust $ head results
      runTest m ()
        [('b', ()), ('d', ())]
    it "should lazily split infinite streams" $ do
      let count = return 0 <|> liftM (+1) count
      runTest (msplit count >>= \(Just (a, _)) -> return a) ()
        [(0, ())]
      runTest (msplit count >>= \(Just (a1, fk)) -> return a1 <|> (msplit fk >>= \(Just (a2, _)) -> return a2)) ()
        [(0, ()), (1, ())]
