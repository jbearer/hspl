{-# LANGUAGE TypeFamilies #-} -- For equational constraints

module DebuggerTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Debugger
import Control.Hspl.Internal.Solver

import Data.List
import Data.Time.Clock
import System.Directory
import System.FilePath

runTest :: Goal -> [String] -> [String] -> IO ()
runTest g commands expectedOutput = do
  tmp <- getTemporaryDirectory

  UTCTime { utctDayTime=ts } <- getCurrentTime

  let config = debugConfig { inputFile = tmp </> "hspl-test-" ++ show ts ++ ".in"
                           , outputFile = tmp </> "hspl-test-" ++ show ts ++ ".out"
                           , interactive = False
                           , coloredOutput = False
                           }
  writeFile (inputFile config) $ unlines commands
  debug config g
  actualOutput <- readFile $ outputFile config
  removeFile $ inputFile config
  removeFile $ outputFile config
  actualOutput `shouldEqual` unlines expectedOutput

expectTrace :: TermData a => String -> Int -> String -> a -> String
expectTrace s d pred arg = "(" ++ show d ++ ") " ++ s ++ ": " ++ show (predicate pred arg)

expectCall :: TermData a => Int -> String -> a -> String
expectCall = expectTrace "Call"

expectRedo :: TermData a => Int -> String -> a -> String
expectRedo = expectTrace "Redo"

expectExit :: TermData a => Int -> String -> a -> String
expectExit = expectTrace "Exit"

expectFail :: TermData a => Int -> String -> a -> String
expectFail = expectTrace "Fail"

expectUnknownPred :: TermData a => Int -> String -> a -> String
expectUnknownPred d pred arg = "(" ++ show d ++ ") Error: Unknown predicate \"" ++
                                pred ++ " :: " ++ show (predType $ predicate pred arg) ++ "\""

expectCanUnifyCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b) =>
                        Int -> a -> b -> String
expectCanUnifyCall d t1 t2 = "(" ++ show d ++ ") Call: " ++ show (CanUnify (toTerm t1) (toTerm t2))

expectCanUnifyExit :: (TermData a) => Int -> a -> String
expectCanUnifyExit d t = "(" ++ show d ++ ") Exit: " ++ show (CanUnify (toTerm t) (toTerm t))

expectCanUnifyFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectCanUnifyFail d t1 t2 = "(" ++ show d ++ ") Fail: " ++ show (CanUnify (toTerm t1) (toTerm t2))

expectIdenticalCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectIdenticalCall d t1 t2 = "(" ++ show d ++ ") Call: " ++ show (Identical (toTerm t1) (toTerm t2))

expectIdenticalExit :: (TermData a) => Int -> a -> String
expectIdenticalExit d t = "(" ++ show d ++ ") Exit: " ++ show (Identical (toTerm t) (toTerm t))

expectIdenticalFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b) =>
                        Int -> a -> b -> String
expectIdenticalFail d t1 t2 = "(" ++ show d ++ ") Fail: " ++ show (Identical (toTerm t1) (toTerm t2))

expectNotCall :: Int -> Goal -> String
expectNotCall d g = "(" ++ show d ++ ") Call: " ++ show (Not g)

expectNotExit :: Int -> Goal -> String
expectNotExit d g = "(" ++ show d ++ ") Exit: " ++ show (Not g)

expectNotFail :: Int -> Goal -> String
expectNotFail d g = "(" ++ show d ++ ") Fail: " ++ show (Not g)

expectEqualCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectEqualCall d a b = "(" ++ show d ++ ") Call: " ++ show (Equal (toTerm a) (toTerm b))

expectEqualExit :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectEqualExit d a b = "(" ++ show d ++ ") Exit: " ++ show (Equal (toTerm a) (toTerm b))

expectEqualFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectEqualFail d a b = "(" ++ show d ++ ") Fail: " ++ show (Equal (toTerm a) (toTerm b))

-- deep(X) :- foo(X).
-- foo(X) :- bar(X).
-- bar(a).
deep = [ HornClause (predicate "deep" (Var "x" :: Var Char))
                    [PredGoal (predicate "foo" (Var "x" :: Var Char))
                              [HornClause (predicate "foo" (Var "x" :: Var Char))
                                                [PredGoal (predicate "bar" (Var "x" :: Var Char))
                                                          [HornClause (predicate "bar" 'a') []]]]]
       ]

-- wide(X, Y, Z) :- foo(X), bar(Y), baz(Z).
-- foo(a).
-- bar(b).
-- baz(c).
wide = [ HornClause ( predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
                    [ PredGoal (predicate "foo" (Var "x" :: Var Char))
                               [HornClause (predicate "foo" 'a') []]
                    , PredGoal (predicate "bar" (Var "y" :: Var Char))
                               [HornClause (predicate "bar" 'b') []]
                    , PredGoal (predicate "baz" (Var "z" :: Var Char))
                               [HornClause (predicate "baz" 'c') []]
                    ]
       ]

-- foo(X) :-
--   bar(X) % Undefined predicate
--   baz(a) % Predicate that fails on input 'a'
-- baz(b).
backtracking = [ HornClause (predicate "foo" (Var "x" :: Var Char))
                            [PredGoal (predicate "bar" (Var "x" :: Var Char)) []]
               , HornClause (predicate "foo" (Var "x" :: Var Char))
                            [PredGoal (predicate "baz" 'a')
                                      [HornClause (predicate "baz" 'b') []]]
               ]

test = describeModule "Control.Hspl.Internal.Debugger" $ do
  describe "the step command" $ do
    let deepGoal = PredGoal (predicate "deep" (Var "x" :: Var Char)) deep
    let deepTrace = [ expectCall 1 "deep" (Var "x" :: Var Char)
                    , expectCall 2 "foo" (Var "x" :: Var Char)
                    , expectCall 3 "bar" (Var "x" :: Var Char)
                    , expectExit 3 "bar" 'a'
                    , expectExit 2 "foo" 'a'
                    , expectExit 1 "deep" 'a'
                    ]
    let wideGoal = PredGoal (predicate "wide"
                      (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide
    let wideTrace = [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
                    , expectCall 2 "foo" (Var "x" :: Var Char)
                    , expectExit 2 "foo" 'a'
                    , expectCall 2 "bar" (Var "y" :: Var Char)
                    , expectExit 2 "bar" 'b'
                    , expectCall 2 "baz" (Var "z" :: Var Char)
                    , expectExit 2 "baz" 'c'
                    , expectExit 1 "wide" ('a', 'b', 'c')
                    ]
    let backtrackingGoal = PredGoal (predicate "foo" (Var "x" :: Var Char)) backtracking
    let backtrackingTrace = [ expectCall 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "bar" (Var "x" :: Var Char)
                            , expectUnknownPred 2 "bar" (Var "x" :: Var Char)
                            , expectFail 1 "foo" (Var "x" :: Var Char)
                            , expectRedo 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "baz" 'a'
                            , expectFail 2 "baz" 'a'
                            , expectFail 1 "foo" (Var "x" :: Var Char)
                            ]
    let canUnifyGoal = CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let canUnifyTrace = [ expectCanUnifyCall 1 (Var "x" :: Var String) "foo"
                        , expectCanUnifyExit 1 "foo"
                        ]
    let canUnifyFailGoal = CanUnify (toTerm "bar") (toTerm "foo")
    let canUnifyFailTrace = [ expectCanUnifyCall 1 "bar" "foo"
                            , expectCanUnifyFail 1 "bar" "foo"
                            ]
    let identicalGoal = Identical (toTerm "foo") (toTerm "foo")
    let identicalTrace = [ expectIdenticalCall 1 "foo" "foo"
                         , expectIdenticalExit 1 "foo"
                         ]
    let identicalFailGoal = Identical (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let identicalFailTrace = [ expectIdenticalCall 1 (Var "x" :: Var String) "foo"
                             , expectIdenticalFail 1 (Var "x" :: Var String) "foo"
                             ]
    let notGoal = Not $ CanUnify (toTerm "bar") (toTerm "foo")
    let notTrace = [ expectNotCall 1 $ CanUnify (toTerm "bar") (toTerm "foo")
                   , expectCanUnifyCall 2 "bar" "foo"
                   , expectCanUnifyFail 2 "bar" "foo"
                   , expectNotExit 1 $ CanUnify (toTerm "bar") (toTerm "foo")
                   ]
    let notFailGoal = Not $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let notFailTrace = [ expectNotCall 1 $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
                       , expectCanUnifyCall 2 (Var "x" :: Var String) "foo"
                       , expectCanUnifyExit 2 "foo"
                       , expectNotFail 1 $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
                       ]
    let equalGoal = Equal (toTerm (Var "x" :: Var Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalTrace = [ expectEqualCall 1 (Var "x" :: Var Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     , expectEqualExit 1 (3 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     ]
    let equalFailGoal = Equal (toTerm (2 :: Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalFailTrace = [ expectEqualCall 1 (2 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                         , expectEqualFail 1 (2 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                         ]
    let run g t c = runTest g (map (const c) [1..length t]) t

    it "should prompt after every step of computation" $ do
      run deepGoal deepTrace "step"
      run wideGoal wideTrace "step"
      run backtrackingGoal backtrackingTrace "step"
      run canUnifyGoal canUnifyTrace "step"
      run canUnifyFailGoal canUnifyFailTrace "step"
      run identicalGoal identicalTrace "step"
      run identicalFailGoal identicalFailTrace "step"
      run notGoal notTrace "step"
      run notFailGoal notFailTrace "step"
      run equalGoal equalTrace "step"
      run equalFailGoal equalFailTrace "step"
    it "should have a one-character alias" $ do
      run deepGoal deepTrace "s"
      run wideGoal wideTrace "s"
      run backtrackingGoal backtrackingTrace "s"
      run canUnifyGoal canUnifyTrace "s"
      run canUnifyFailGoal canUnifyFailTrace "s"
      run identicalGoal identicalTrace "s"
      run identicalFailGoal identicalFailTrace "s"
      run notGoal notTrace "s"
      run notFailGoal notFailTrace "s"
      run equalGoal equalTrace "s"
      run equalFailGoal equalFailTrace "s"

  describe "the next command" $ do
    it "should skip to the next event at the current depth" $ do
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["next", "next"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectExit 1 "deep" 'a'
        ]
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["next", "next"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["step", "next", "next", "next", "next", "next", "next", "next"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 2 "foo" 'a'
        , expectCall 2 "bar" (Var "y" :: Var Char)
        , expectExit 2 "bar" 'b'
        , expectCall 2 "baz" (Var "z" :: Var Char)
        , expectExit 2 "baz" 'c'
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]
    it "if no more events at the current depth, it should stop at the next decrease in depth" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["step", "next", "next", "next"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 2 "foo" 'a'
        , expectExit 1 "deep" 'a'
        ]
    it "should have a one-character alias" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["n", "n"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectExit 1 "deep" 'a'
        ]

  describe "the finish command" $ do
    it "should skip to the next decrease in depth" $ do
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["step", "finish", "step"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]
      runTest (PredGoal (predicate "foo" (Var "x" :: Var Char)) backtracking)
        ["step", "finish", "finish"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectCall 2 "bar" (Var "x" :: Var Char)
        , expectFail 1 "foo" (Var "x" :: Var Char)
        ]
    it "should have a one-character alias" $
        runTest (PredGoal (predicate "wide"
                  (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["s", "f", "s"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]

  describe "the help command" $
    it "should print a usage message" $ do
      let run comm = runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
                      [comm, "f"]
                      [ expectCall 1 "deep" (Var "x" :: Var Char)
                      , debugHelp
                      ]
      run "?"
      run "h"
      run "help"

  describe "a blank command" $
    it "should repeat the previous command" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["n", ""]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectExit 1 "deep" 'a'
        ]

  describe "an unknown command" $
    it "should trigger a retry prompt" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["bogus", "finish"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , "Unknown command \"bogus\". Try \"?\" for help."
        ]
