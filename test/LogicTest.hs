{-# LANGUAGE TupleSections #-}

module LogicTest where

import Testing
import Control.Hspl.Internal.Logic

import Control.Applicative
import Data.Maybe

runTest :: (Show a, Eq a, Show s, Eq s, SplittableState s) => Logic s a -> s -> [(a, s)] -> Expectation
runTest m s expected =
  let (expectedResults, expectedStates) = unzip expected
  in do
    observeAllLogic m s `shouldBe` expectedResults
    execAllLogic m s `shouldBe` expectedStates
    runAllLogic m s `shouldBe` expected

    observeManyLogic 999 m s `shouldBe` expectedResults
    execManyLogic 999 m s `shouldBe` expectedStates
    runManyLogic 999 m s `shouldBe` expected

test = describeModule "Control.Hspl.Internal.Logic" $ do
  describe "mplus" $ do
    it "should yield multiple results" $
      runTest (return 'a' `mplus` return 'b') (LogicState 'x' 'y')
        [('a', LogicState 'x' 'y'), ('b', LogicState 'x' 'y')]
    it "should backtrack the backtracking state" $
      runTest ((put (Backtracking 's') >> gets backtracking) `mplus` gets backtracking) (Backtracking 'x')
        [('s', Backtracking 's'), ('x', Backtracking 'x')]
    it "should not backtrack the global state" $
      runTest ((put (Global 's') >> gets global) `mplus` gets global) (Global 'y')
        [('s', Global 's'), ('s', Global 's')]
    it "should return global state at the time the solution was evaluated" $
      runTest ((put (Global 'a') >> gets global) `mplus` (put (Global 'b') >> gets global)) (Global 'y')
        [('a', Global 'a'), ('b', Global 'b')]

  describe "binding" $ do
    it "should apply a function to each current result" $
      runTest ((return 'a' <|> return 'b') >>= (return . (:"z")) :: Logic () String) ()
        [("az", ()), ("bz", ())]
    it "should thread backtracking state" $ do
      runTest ((put (Backtracking 'a') <|> put (Backtracking 'b')) >>= const (gets backtracking)) (Backtracking 'z')
        [('a', Backtracking 'a'), ('b', Backtracking 'b')]
      runTest (put (Backtracking 'a') >>= const (return 'b' <|> gets backtracking)) (Backtracking 'z')
        [('b', Backtracking 'a'), ('a', Backtracking 'a')]
    it "should thread global state" $ do
      runTest ((modify (+1) <|> modify (+2)) >>= const (gets global <* modify (+1))) (Global 0)
        [(1 :: Int, Global 2), (4, Global 5)]
      runTest (put (Global 'a') >>= const (return 'b' <|> gets global)) (Global 'z')
        [('b', Global 'a'), ('a', Global 'a')]

  describe "cut" $ do
    it "should discard all choice points in the topmost frame" $ do
      runTest (return 'a' <|> commit 'b' <|> return 'c') ()
        [('a', ()), ('b', ())]
      runTest ((return 'a' <|> return 'b') >>= \c -> commit [c, 'y'] <|> return [c, 'z']) ()
        [("ay", ())]
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
      runTest (cutFrame (commit 'a' <|> return 'b') <|> return 'c') ()
        [('a', ()), ('c', ())]
      runTest (cutFrame ((return 'a' <|> return 'b') >>= \c -> commit [c, 'y'] <|> return [c, 'z']) <|> return "foo") ()
        [("ay", ()), ("foo", ())]

  describe "mzero" $ do
    it "should abort the current branch and backtrack" $ do
      runTest (return 'a' <|> mzero <|> return 'c') (LogicState 'x' 'y')
        [('a', LogicState 'x' 'y'), ('c', LogicState 'x' 'y')]
      runTest ((return 'a' <|> return 'b') >>= \c -> mzero <|> return c) (LogicState 'x' 'y')
        [('a', LogicState 'x' 'y'), ('b', LogicState 'x' 'y')]
    it "should persist modifications to global state" $
      runTest ((put (Global 'z') >> mzero) <|> gets global) (Global 'x')
        [('z', Global 'z')]
    it "should not persist modifications to backtracking state" $
      runTest ((put (Backtracking 'z') >> mzero) <|> gets backtracking) (Backtracking 'x')
        [('x', Backtracking 'x')]

  describe "runMany" $ do
    withParams [[], ['a'], ['a', 'b']] $ \results ->
      it "should return all results when there are at most the expected number" $ do
        let m = msum $ map return results
        runManyLogic 2 m (LogicState 's' 't') `shouldBe` map (, LogicState 's' 't') results
        execManyLogic 2 m (LogicState 's' 't') `shouldBe` map (const $ LogicState 's' 't') results
        observeManyLogic 2 m (LogicState 's' 't') `shouldBe` results
    withParams ["abc", "abcd"] $ \results ->
      it "should return at most the requested number of results" $ do
        let m = msum $ map return results
        runManyLogic 2 m (LogicState 's' 't') `shouldBe` map (, LogicState 's' 't') (take 2 results)
        execManyLogic 2 m (LogicState 's' 't') `shouldBe` replicate 2 (LogicState 's' 't')
        observeManyLogic 2 m (LogicState 's' 't') `shouldBe` take 2 results
    withParams [-1, 0] $ \count ->
      it "should return an empty list when zero or fewer results are requested" $ do
        runManyLogic count (return 'a') (LogicState 's' 't') `shouldBe` []
        execManyLogic count (return 'a') (LogicState 's' 't') `shouldBe` []
        observeManyLogic count (return 'a') (LogicState 's' 't') `shouldBe` []
    it "should properly thread backtracking state" $
      runManyLogic 2 (put (Backtracking 'a') >> (return 'b' <|> gets backtracking)) (Backtracking 's') `shouldBe`
        [('b', Backtracking 'a'), ('a', Backtracking 'a')]
    it "should properly thread global state" $ do
      runManyLogic 2 (put (Global 'a') >> (return 'b' <|> gets global)) (Global 's') `shouldBe`
        [('b', Global 'a'), ('a', Global 'a')]
      runManyLogic 2 ((put (Global 'a') >> return 'b') <|> gets global) (Global 's') `shouldBe`
        [('b', Global 'a'), ('a', Global 'a')]
    it "should maintain the cut stack between alternatives" $
      observeManyLogic 4 (cutFrame (return 'a' <|> commit 'b' <|> return 'c') <|> return 'd') ()
        `shouldBe` "abd"

  describe "msplit" $ do
    it "should return the first result of a nondeterministic computation" $ do
      let results = observeAllLogic (msplit $ return 'a' <|> return 'b') ()
      length results `shouldBe` 1
      guard $ isJust $ head results
      fst (fromJust $ head results) `shouldBe` 'a'
    it "should return Nothing when there are no results" $ do
      let results = observeAllLogic (msplit mzero) ()
      length results `shouldBe` 1
      guard (isNothing $ head results)
    it "should return a suspension which yields the rest of the results" $ do
      let results = observeAllLogic (msplit $ return 'a' <|> return 'b') ()
      length results `shouldBe` 1
      guard $ isJust $ head results
      let m = snd $ fromJust $ head results
      runTest m ()
        [('b', ())]
    it "should preserve global state" $
      runTest (put (Global 'a') >> msplit (return 'z') >>=
               \m -> liftM2 (,) (gets global) (return $ fst $ fromJust m)) (Global 's')
        [(('a', 'z'), Global 'a')]
    it "should preserve backtracking state" $
      runTest ((put (Backtracking 'a') <|> put (Backtracking 'b')) >> msplit (return 'z') >>=
               \m -> liftM2 (,) (gets backtracking) (return $ fst $ fromJust m)) (Backtracking 's')
        [(('a', 'z'), Backtracking 'a'), (('b', 'z'), Backtracking 'b')]
    it "should preserve the cut stack" $
      runTest (cutFrame (msplit (return 'a' <|> return 'b') >>= commit . fst . fromJust) <|> return 'c') ()
        [('a', ()), ('c', ())]
    it "should preserve the cut stack in the suspension" $ do
      let results = observeAllLogic (msplit $ cutFrame (return 'a' <|> commit 'b' <|> return 'c') <|> return 'd') ()
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
