module DebuggerTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Debugger
import Control.Hspl.Internal.Solver

import Data.List
import Data.Time.Clock
import System.Directory
import System.FilePath

runTest :: Program -> Goal -> [String] -> [String] -> IO ()
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

deepProgram = addClauses [ HornClause (predicate "foo" (Var "x" :: Var Char))
                                      [predicate "bar" (Var "x" :: Var Char)]
                         , HornClause (predicate "bar" (Var "x" :: Var Char))
                                      [predicate "baz" (Var "x" :: Var Char)]
                         , HornClause (predicate "baz" 'a') []
                         ] emptyProgram

wideProgram = addClauses [ HornClause ( predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
                                      [ predicate "foo" (Var "x" :: Var Char)
                                      , predicate "bar" (Var "y" :: Var Char)
                                      , predicate "baz" (Var "z" :: Var Char)
                                      ]
                         , HornClause ( predicate "foo" 'a') []
                         , HornClause ( predicate "bar" 'b') []
                         , HornClause ( predicate "baz" 'c') []
                         ] emptyProgram

backtrackingProgram = addClauses [ HornClause (predicate "foo" (Var "x" :: Var Char))
                                              [predicate "bar" (Var "x" :: Var Char)]
                                 , HornClause (predicate "foo" (Var "x" :: Var Char))
                                              [predicate "baz" 'a']
                                 , HornClause ( predicate "baz" 'b') []
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
                            , expectRedo 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "bar" (Var "x" :: Var Char)
                            , expectFail 2 "bar" (Var "x" :: Var Char)
                            ]
    let run p g t c = runTest p g (map (const c) [1..length t]) t

    it "should prompt after every step of computation" $ do
      run deepProgram deepGoal deepTrace "step"
      run wideProgram wideGoal wideTrace "step"
      run backtrackingProgram backtrackingGoal backtrackingTrace "step"
    it "should have a one-character alias" $ do
      run deepProgram deepGoal deepTrace "s"
      run wideProgram wideGoal wideTrace "s"
      run backtrackingProgram backtrackingGoal backtrackingTrace "s"

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
        , expectRedo 1 "foo" (Var "x" :: Var Char)
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
