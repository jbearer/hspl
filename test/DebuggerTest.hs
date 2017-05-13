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

runTest :: Program -> Predicate -> [String] -> [String] -> IO ()
runTest p g commands expectedOutput = do
  tmp <- getTemporaryDirectory

  UTCTime { utctDayTime=ts } <- getCurrentTime

  let config = debugConfig { inputFile = tmp </> "hspl-test-" ++ show ts ++ ".in"
                           , outputFile = tmp </> "hspl-test-" ++ show ts ++ ".out"
                           , interactive = False
                           , coloredOutput = False
                           }
  writeFile (inputFile config) $ unlines commands
  debug config p g
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

deepProgram = addClauses [ HornClause (predicate "foo" (Var "x" :: Var Char))
                                      [PredGoal $ predicate "bar" (Var "x" :: Var Char)]
                         , HornClause (predicate "bar" (Var "x" :: Var Char))
                                      [PredGoal $ predicate "baz" (Var "x" :: Var Char)]
                         , HornClause (predicate "baz" 'a') []
                         ] emptyProgram

wideProgram = addClauses [ HornClause ( predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
                                      [ PredGoal $ predicate "foo" (Var "x" :: Var Char)
                                      , PredGoal $ predicate "bar" (Var "y" :: Var Char)
                                      , PredGoal $ predicate "baz" (Var "z" :: Var Char)
                                      ]
                         , HornClause ( predicate "foo" 'a') []
                         , HornClause ( predicate "bar" 'b') []
                         , HornClause ( predicate "baz" 'c') []
                         ] emptyProgram

backtrackingProgram = addClauses [ HornClause (predicate "foo" (Var "x" :: Var Char))
                                              [PredGoal $ predicate "bar" (Var "x" :: Var Char)]
                                 , HornClause (predicate "foo" (Var "x" :: Var Char))
                                              [PredGoal $ predicate "baz" 'a']
                                 , HornClause ( predicate "baz" 'b') []
                                 ] emptyProgram

canUnifyProgram = addClauses [ HornClause ( predicate "isFoo" (Var "x" :: Var String))
                                          [ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")]
                             ] emptyProgram

identicalProgram = addClauses [ HornClause ( predicate "isFoo" (Var "x" :: Var String))
                                           [ Identical (toTerm (Var "x" :: Var String)) (toTerm "foo")]
                              ] emptyProgram

notProgram = addClauses [ HornClause ( predicate "isNotFoo" (Var "x" :: Var String))
                                     [ Not $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")]
                        ] emptyProgram

equalProgram = addClauses [ HornClause (predicate "equal" (Var "x" :: Var Int, Var "y" :: Var Int))
                                       [Equal (toTerm (Var "x" :: Var Int)) (toTerm (Var "y" :: Var Int))]
                          ] emptyProgram

test = describeModule "Control.Hspl.Internal.Debugger" $ do
  describe "the step command" $ do
    let deepGoal = predicate "foo" (Var "x" :: Var Char)
    let deepTrace = [ expectCall 1 "foo" (Var "x" :: Var Char)
                    , expectCall 2 "bar" (Var "x" :: Var Char)
                    , expectCall 3 "baz" (Var "x" :: Var Char)
                    , expectExit 3 "baz" 'a'
                    , expectExit 2 "bar" 'a'
                    , expectExit 1 "foo" 'a'
                    ]
    let wideGoal = predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
    let wideTrace = [ expectCall 1 "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
                    , expectCall 2 "foo" (Var "x" :: Var Char)
                    , expectExit 2 "foo" 'a'
                    , expectCall 2 "bar" (Var "y" :: Var Char)
                    , expectExit 2 "bar" 'b'
                    , expectCall 2 "baz" (Var "z" :: Var Char)
                    , expectExit 2 "baz" 'c'
                    , expectExit 1 "p" ('a', 'b', 'c')
                    ]
    let backtrackingGoal = predicate "foo" (Var "x" :: Var Char)
    let backtrackingTrace = [ expectCall 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "baz" 'a'
                            , expectFail 2 "baz" 'a'
                            , expectFail 1 "foo" (Var "x" :: Var Char)
                            , expectRedo 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "bar" (Var "x" :: Var Char)
                            , expectUnknownPred 2 "bar" (Var "x" :: Var Char)
                            , expectFail 1 "foo" (Var "x" :: Var Char)
                            ]
    let canUnifyGoal = predicate "isFoo" (Var "x" :: Var String)
    let canUnifyTrace = [ expectCall 1 "isFoo" (Var "x" :: Var String)
                        , expectCanUnifyCall 2 (Var "x" :: Var String) "foo"
                        , expectCanUnifyExit 2 "foo"
                        , expectExit 1 "isFoo" "foo"
                        ]
    let canUnifyFailGoal = predicate "isFoo" "bar"
    let canUnifyFailTrace = [ expectCall 1 "isFoo" "bar"
                            , expectCanUnifyCall 2 "bar" "foo"
                            , expectCanUnifyFail 2 "bar" "foo"
                            , expectFail 1 "isFoo" "bar"
                            ]
    let identicalGoal = predicate "isFoo" "foo"
    let identicalTrace = [ expectCall 1 "isFoo" "foo"
                         , expectIdenticalCall 2 "foo" "foo"
                         , expectIdenticalExit 2 "foo"
                         , expectExit 1 "isFoo" "foo"
                         ]
    let identicalFailGoal = predicate "isFoo" (Var "x" :: Var String)
    let identicalFailTrace = [ expectCall 1 "isFoo" (Var "x" :: Var String)
                             , expectIdenticalCall 2 (Var "x" :: Var String) "foo"
                             , expectIdenticalFail 2 (Var "x" :: Var String) "foo"
                             , expectFail 1 "isFoo" (Var "x" :: Var String)
                             ]
    let notGoal = predicate "isNotFoo" "bar"
    let notTrace = [ expectCall 1 "isNotFoo" "bar"
                   , expectNotCall 2 $ CanUnify (toTerm "bar") (toTerm "foo")
                   , expectCanUnifyCall 3 "bar" "foo"
                   , expectCanUnifyFail 3 "bar" "foo"
                   , expectNotExit 2 $ CanUnify (toTerm "bar") (toTerm "foo")
                   , expectExit 1 "isNotFoo" "bar"
                   ]
    let notFailGoal = predicate "isNotFoo" (Var "x" :: Var String)
    let notFailTrace = [ expectCall 1 "isNotFoo" (Var "x" :: Var String)
                       , expectNotCall 2 $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
                       , expectCanUnifyCall 3 (Var "x" :: Var String) "foo"
                       , expectCanUnifyExit 3 "foo"
                       , expectNotFail 2 $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
                       , expectFail 1 "isNotFoo" (Var "x" :: Var String)
                       ]
    let equalGoal = predicate "equal" (Var "x" :: Var Int, Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalTrace = [ expectCall 1 "equal" (Var "x" :: Var Int, Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     , expectEqualCall 2 (Var "x" :: Var Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     , expectEqualExit 2 (3 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     , expectExit 1 "equal" (3 :: Int, Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     ]
    let run p g t c = runTest p g (map (const c) [1..length t]) t

    it "should prompt after every step of computation" $ do
      run deepProgram deepGoal deepTrace "step"
      run wideProgram wideGoal wideTrace "step"
      run backtrackingProgram backtrackingGoal backtrackingTrace "step"
      run canUnifyProgram canUnifyGoal canUnifyTrace "step"
      run canUnifyProgram canUnifyFailGoal canUnifyFailTrace "step"
      run identicalProgram identicalGoal identicalTrace "step"
      run identicalProgram identicalFailGoal identicalFailTrace "step"
      run notProgram notGoal notTrace "step"
      run notProgram notFailGoal notFailTrace "step"
      run equalProgram equalGoal equalTrace "step"
    it "should have a one-character alias" $ do
      run deepProgram deepGoal deepTrace "s"
      run wideProgram wideGoal wideTrace "s"
      run backtrackingProgram backtrackingGoal backtrackingTrace "s"
      run canUnifyProgram canUnifyGoal canUnifyTrace "s"
      run canUnifyProgram canUnifyFailGoal canUnifyFailTrace "s"
      run identicalProgram identicalGoal identicalTrace "s"
      run identicalProgram identicalFailGoal identicalFailTrace "s"
      run notProgram notGoal notTrace "s"
      run notProgram notFailGoal notFailTrace "s"
      run equalProgram equalGoal equalTrace "step"

  describe "the next command" $ do
    it "should skip to the next event at the current depth" $ do
      runTest deepProgram (predicate "foo" (Var "x" :: Var Char))
        ["next", "next"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectExit 1 "foo" 'a'
        ]
      runTest wideProgram (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
        ["next", "next"]
        [ expectCall 1 "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectExit 1 "p" ('a', 'b', 'c')
        ]
      runTest wideProgram (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
        ["step", "next", "next", "next", "next", "next", "next", "next"]
        [ expectCall 1 "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 2 "foo" 'a'
        , expectCall 2 "bar" (Var "y" :: Var Char)
        , expectExit 2 "bar" 'b'
        , expectCall 2 "baz" (Var "z" :: Var Char)
        , expectExit 2 "baz" 'c'
        , expectExit 1 "p" ('a', 'b', 'c')
        ]
    it "if no more events at the current depth, it should stop at the next decrease in depth" $
      runTest deepProgram (predicate "foo" (Var "x" :: Var Char))
        ["step", "next", "next", "next"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectCall 2 "bar" (Var "x" :: Var Char)
        , expectExit 2 "bar" 'a'
        , expectExit 1 "foo" 'a'
        ]
    it "should have a one-character alias" $
      runTest deepProgram (predicate "foo" (Var "x" :: Var Char))
        ["n", "n"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectExit 1 "foo" 'a'
        ]

  describe "the finish command" $ do
    it "should skip to the next decrease in depth" $ do
      runTest wideProgram (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
        ["step", "finish", "step"]
        [ expectCall 1 "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 1 "p" ('a', 'b', 'c')
        ]
      runTest backtrackingProgram (predicate "foo" (Var "x" :: Var Char))
        ["step", "finish", "finish"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectCall 2 "baz" 'a'
        , expectFail 1 "foo" (Var "x" :: Var Char)
        ]
    it "should have a one-character alias" $
        runTest wideProgram (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
        ["s", "f", "s"]
        [ expectCall 1 "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 1 "p" ('a', 'b', 'c')
        ]

  describe "the help command" $
    it "should print a usage message" $ do
      let run comm = runTest deepProgram (predicate "foo" (Var "x" :: Var Char))
                      [comm, "f"]
                      [ expectCall 1 "foo" (Var "x" :: Var Char)
                      , debugHelp
                      ]
      run "?"
      run "h"
      run "help"

  describe "a blank command" $
    it "should repeat the previous command" $
      runTest deepProgram (predicate "foo" (Var "x" :: Var Char))
        ["n", ""]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectExit 1 "foo" 'a'
        ]

  describe "an unknown command" $
    it "should trigger a retry prompt" $
      runTest deepProgram (predicate "foo" (Var "x" :: Var Char))
        ["bogus", "finish"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , "Unknown command \"bogus\". Try \"?\" for help."
        ]
