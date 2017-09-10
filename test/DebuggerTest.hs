{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraints

module DebuggerTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Debugger
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.UI

import Control.Exception
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Identity hiding (when)
import Control.Monad.State hiding (when)
import Control.Monad.Writer (MonadWriter (..), Writer, execWriter)
import Data.Either
import Data.List
import Data.Monoid ((<>))
import Text.Parsec.Pos
import Text.Parsec.Error

-- For tests involving Parsec error messages
deriving instance Show Message

runTest :: Goal -> [String] -> Trace a -> IO ()
runTest g commands expectedTrace = tempFile2 $ \inFile outFile -> do
  let expectedOutput = runTrace expectedTrace
  let config = debugConfig { inputFile = inFile
                           , outputFile = outFile
                           , interactive = False
                           , coloredOutput = False
                           }
  writeFile inFile $ unlines commands

  result <- try $ debug config g
  output <- readFile outFile
  case result of
    Right _ -> return ()
    Left e ->
      failure $ "uncaught exeption: " ++ show (e :: IOException) ++
                "\n--- begin captured stdout ---\n" ++
                output ++
                "\n--- end captured stdout ---\n"
  output `shouldEqual` unlines expectedOutput

data TraceState = TraceState { depth :: Int
                             , depthType :: DepthType
                             , lastMsg :: String
                             }

type Trace = StateT TraceState (Writer [String])

data DepthType = Ascending | Descending | Fixed

runTrace :: Trace a -> [String]
runTrace m = execWriter $ evalStateT m TraceState { depth=1, depthType=Fixed, lastMsg="" }

setDepth :: Int -> Trace ()
setDepth d = modify $ \ts -> ts { depth = d, depthType = Fixed }

descend :: Trace Int
descend = do
  modify $ \s@TraceState { depth = d, depthType = t } -> case t of
    Descending -> s { depth = d + 1, depthType = Descending }
    _ -> s { depth = d, depthType = Descending }
  gets depth

ascend :: Trace Int
ascend = do
  modify $ \s@TraceState { depth = d, depthType = t } -> case t of
    Ascending -> s { depth = d - 1, depthType = Ascending }
    _ -> s { depth = d, depthType = Ascending }
  gets depth

traceLines :: [String] -> Trace ()
traceLines msg = lift (tell msg) >> modify (\s -> s { lastMsg = last msg })

trace :: String -> Trace ()
trace = traceLines . (:[])

traceInfoLines :: [String] -> Trace ()
traceInfoLines msg = do
  prev <- gets lastMsg
  tell $ msg ++ [prev]

traceInfo :: String -> Trace ()
traceInfo = traceInfoLines . (:[])

traceCall :: Goal -> Trace ()
traceCall g = do
  d <- descend
  trace $ "(" ++ show d ++ ") Call: " ++ formatGoal g

traceRedo :: Goal -> Trace ()
traceRedo g = do
  d <- descend
  trace $ "(" ++ show d ++ ") Redo: " ++ formatGoal g

traceExit :: Goal -> Trace ()
traceExit g = do
  d <- ascend
  trace $ "(" ++ show d ++ ") Exit: " ++ formatGoal g

traceFail :: Goal -> Trace ()
traceFail g = do
  d <- ascend
  trace $ "(" ++ show d ++ ") Fail: " ++ formatGoal g

traceUnknownPred :: Predicate -> Trace ()
traceUnknownPred p@(Predicate name arg) = do
  d <- ascend
  trace $ "(" ++ show d ++ ") Error: Unknown predicate \"" ++ name ++ " :: " ++ formatType (predType p) ++ "\""

-- deep(X) :- foo(X).
-- foo(X) :- bar(X).
-- bar(a).
deep = [ HornClause (predicate "deep" (Var "x" :: Var Char))
                    (PredGoal (predicate "foo" (Var "x" :: Var Char))
                              [HornClause (predicate "foo" (Var "x" :: Var Char))
                                                (PredGoal (predicate "bar" (Var "x" :: Var Char))
                                                          [HornClause (predicate "bar" 'a') Top])])
       ]

-- wide(X, Y, Z) :- foo(X), bar(Y), baz(Z).
-- foo(a).
-- bar(b).
-- baz(c).
wide = [ HornClause (  predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
                    (  PredGoal (predicate "foo" (Var "x" :: Var Char))
                                [HornClause (predicate "foo" 'a') Top]
                    <> PredGoal (predicate "bar" (Var "y" :: Var Char))
                                [HornClause (predicate "bar" 'b') Top]
                    <> PredGoal (predicate "baz" (Var "z" :: Var Char))
                                [HornClause (predicate "baz" 'c') Top]
                    )
       ]

-- foo(X) :-
--   bar(X) % Undefined predicate
--   baz(a) % Predicate that fails on input 'a'
-- baz(b).
backtracking = [ HornClause (predicate "foo" (Var "x" :: Var Char))
                            (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])
               , HornClause (predicate "foo" (Var "x" :: Var Char))
                            (PredGoal (predicate "baz" 'a')
                                      [HornClause (predicate "baz" 'b') Top])
               ]

test = describeModule "Control.Hspl.Internal.Debugger" $ do
  describe "the command parser" $ do
    -- This will be ignored by the parser, but we need it to run the coroutine
    let context = DC { stack = []
                     , status = Call
                     , msg = ""
                     }
    let runTest input expected =
          do let st = pogoStick (\(Await f) -> f (Just context)) $ parseCommand input
             output <- runDebugStateT debugConfig st
             output `shouldBe` Right expected
    let shouldFail input err =
          do let st = pogoStick (\(Await f) -> f (Just context)) $ parseCommand input
             output <- runDebugStateT debugConfig st
             case output of
                Right c -> failure $ "Expected parser to fail on input \"" ++ input ++ "\" with " ++
                                     "error (" ++ show err ++
                                     "), but it succeeded and produced " ++ show c
                Left e -> if err `elem` errorMessages e
                            then success
                            else failure $ "Expected parser to fail on input \"" ++ input ++
                                           "\" with error (" ++ show err ++ "), but it failed with " ++
                                          show (errorMessages e)
    -- ([aliases], command)
    withParams [ (["s", "step"], Step)
               , (["n", "next"], Next)
               , (["f", "finish"], Finish)
               , (["c", "continue"], Continue)
               , (["bs", "breakpoints"], InfoBreakpoints)
               , (["gs", "goals"], InfoStack Nothing)
               , (["g", "goal"], InfoStack $ Just 1)
               , (["h", "?", "help"], Help)
               ] $ \(inputs, expected) ->
      it "should parse valid debugger commands with no arguments" $
        forM_ inputs $ \input ->
          runTest input expected
    when "parsing commands with arguments" $
      -- ([aliases], [args], command)
      withParams [ (["gs", "goals"], ["3"], InfoStack $ Just 3)
                 , (["b", "break"], ["foo"], SetBreakpoint "foo")
                 , (["db", "delete-breakpoint"], ["foo"], DeleteBreakpoint $ Left "foo")
                 , (["db", "delete-breakpoint"], ["1"], DeleteBreakpoint $ Right 1)
                 ] $ \(inputs, args, command) -> do
        it "should parse a valid command line" $
          forM_ inputs $ \input ->
            runTest (input ++ " " ++ unwords args) command
        it "should accept extra whitespace" $
          forM_ inputs $ \input ->
            runTest (input ++ "  " ++ intercalate "  " args) command
        it "should fail when the command is not separated from the arguments" $
          forM_ inputs $ \input ->
            shouldFail (input ++ unwords args) (Expect "command")
    when "parsing the goals command" $
      withParams ["a", "1a", "a1", "1.5"] $ \arg ->
        it "should reject invalid arguments" $
          shouldFail ("goals " ++ arg) (Expect "integer")
    withParams [" s", "s ", " s ", "\ts", "s\t", "\ts\t", " s\t", "\t s "] $ \input ->
      it "should ignore whitespace" $
        runTest input Step
    it "should fail when given an unexpected token" $
      shouldFail "step next" (UnExpect "'n'")
    it "should fail when given an unknown command" $
      shouldFail "bogus" (Expect "command")
    it "should output the previous command when given a blank line" $ do
        freshState <- initTerminalState debugConfig
        let state = freshState { lastCommand = Finish }
        let m = pogoStick (\(Await f) -> f (Just context)) $ parseCommand ""
        output <- evalStateT m state
        output `shouldBe` Right Finish

  describe "the step command" $ do
    let deepGoal = PredGoal (predicate "deep" (Var "x" :: Var Char)) deep
    let deepTrace = do
          traceCall deepGoal
          traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          traceCall $ PredGoal (predicate "bar" (Var "x" :: Var Char)) []
          traceExit $ PredGoal (predicate "bar" 'a') []
          traceExit $ PredGoal (predicate "foo" 'a') []
          traceExit $ PredGoal (predicate "deep" 'a') []
    let wideGoal = PredGoal (predicate "wide"
                      (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide
    let wideTrace = do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          traceExit $ PredGoal (predicate "foo" 'a') []
          traceCall $ PredGoal (predicate "bar" (Var "y" :: Var Char)) []
          traceExit $ PredGoal (predicate "bar" 'b') []
          traceCall $ PredGoal (predicate "baz" (Var "z" :: Var Char)) []
          traceExit $ PredGoal (predicate "baz" 'c') []
          traceExit $ PredGoal (predicate "wide" ('a', 'b', 'c')) []
    let backtrackingGoal = PredGoal (predicate "foo" (Var "x" :: Var Char)) backtracking
    let backtrackingTrace = do
          traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          traceCall $ PredGoal (predicate "bar" (Var "x" :: Var Char)) []
          traceUnknownPred $ predicate "bar" (Var "x" :: Var Char)
          traceFail $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          traceRedo $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          traceCall $ PredGoal (predicate "baz" 'a') []
          traceFail $ PredGoal (predicate "baz" 'a') []
          traceFail $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
    let canUnifyGoal = CanUnify (toTerm $ Var "x") (toTerm "foo")
    let canUnifyTrace = do
          traceCall canUnifyGoal
          traceExit $ CanUnify (toTerm "foo") (toTerm "foo")
    let canUnifyFailGoal = CanUnify (toTerm "bar") (toTerm "foo")
    let canUnifyFailTrace = do
          traceCall canUnifyFailGoal
          traceFail canUnifyFailGoal
    let identicalGoal = Identical (toTerm "foo") (toTerm "foo")
    let identicalTrace = do
          traceCall identicalGoal
          traceExit identicalGoal
    let identicalFailGoal = Identical (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let identicalFailTrace = do
          traceCall identicalFailGoal
          traceFail identicalFailGoal
    let equalGoal = Equal (toTerm (Var "x" :: Var Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalTrace = do
          traceCall equalGoal
          traceExit $ Equal (toTerm (3 :: Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalFailGoal = Equal (toTerm (2 :: Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalFailTrace = do
          traceCall equalFailGoal
          traceFail equalFailGoal
    let lessThanGoal = LessThan (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
    let lessThanTrace = do
          traceCall $ LessThan (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                               (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
          traceExit $ LessThan (toTerm (5 :: Int)) (toTerm (6 :: Int))
    let lessThanFailGoal = LessThan (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                     (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
    let lessThanFailTrace = do
          traceCall lessThanFailGoal
          traceFail lessThanFailGoal
    let isUnifiedGoal = IsUnified $ toTerm 'a'
    let isUnifiedTrace = traceCall isUnifiedGoal >> traceExit isUnifiedGoal
    let isUnifiedFailGoal = IsUnified $ toTerm (Var "x" :: Var Char)
    let isUnifiedFailTrace = traceCall isUnifiedFailGoal >> traceFail isUnifiedFailGoal
    let isVariableGoal = IsVariable $ toTerm (Var "x" :: Var Char)
    let isVariableTrace = traceCall isVariableGoal >> traceExit isVariableGoal
    let isVariableFailGoal = IsVariable $ Sum (toTerm (Var "x" :: Var Int)) (toTerm (0 :: Int))
    let isVariableFailTrace = traceCall isVariableFailGoal >> traceFail isVariableFailGoal
    let notGoal = Not Bottom
    let notTrace = do
          traceCall notGoal
          traceCall Bottom
          traceFail Bottom
          traceExit notGoal
    let notFailGoal = Not Top
    let notFailTrace = do
          traceCall notFailGoal
          traceCall Top
          traceExit Top
          traceFail notFailGoal
    let andGoal = And (CanUnify (toTerm "foo") (toTerm $ Var "x"))
                      (Identical (toTerm "foo") (toTerm $ Var "x"))
    let andTrace = do
          traceCall $ CanUnify (toTerm "foo") (toTerm $ Var "x")
          traceExit $ CanUnify (toTerm "foo") (toTerm "foo")
          traceCall $ Identical (toTerm "foo") (toTerm "foo")
          traceExit $ Identical (toTerm "foo") (toTerm "foo")
    let andFailLeftGoal = And Bottom Top
    let andFailLeftTrace = traceCall Bottom >> traceFail Bottom
    let andFailRightGoal = And Top Bottom
    let andFailRightTrace = do
          traceCall Top
          traceExit Top
          traceCall Bottom
          traceFail Bottom
    let orLeftGoal = Or Top Bottom
    let orLeftTrace = do
          traceCall orLeftGoal
          traceCall Top
          traceExit Top
          traceExit orLeftGoal
          traceRedo orLeftGoal
          traceCall Bottom
          traceFail Bottom
          traceFail orLeftGoal
    let orRightGoal = Or Bottom Top
    let orRightTrace = do
          traceCall orRightGoal
          traceCall Bottom
          traceFail Bottom
          traceFail orRightGoal
          traceRedo orRightGoal
          traceCall Top
          traceExit Top
          traceExit orRightGoal
    let orFailGoal = Or Bottom Bottom
    let orFailTrace = do
          traceCall orFailGoal
          traceCall Bottom
          traceFail Bottom
          traceFail orFailGoal
          traceRedo orFailGoal
          traceCall Bottom
          traceFail Bottom
          traceFail orFailGoal
    let alternativesOrGoal = Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                (CanUnify (toTerm $ Var "x") (toTerm 'b'))
    let alternativesGoal = Alternatives (toTerm (Var "x" :: Var Char)) alternativesOrGoal (toTerm $ Var "xs")
    let alternativesTrace = do
          traceCall alternativesGoal
          traceCall alternativesOrGoal
          traceCall $ CanUnify (toTerm $ Var "x") (toTerm 'a')
          traceExit $ CanUnify (toTerm 'a') (toTerm 'a')
          traceExit $ Or (CanUnify (toTerm 'a') (toTerm 'a'))
                         (CanUnify (toTerm $ Var "x") (toTerm 'b'))
          traceRedo alternativesOrGoal
          traceCall $ CanUnify (toTerm $ Var "x") (toTerm 'b')
          traceExit $ CanUnify (toTerm 'b') (toTerm 'b')
          traceExit $ Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                         (CanUnify (toTerm 'b') (toTerm 'b'))
          traceExit $ Alternatives (toTerm $ Var "x")
                                   (Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                       (CanUnify (toTerm $ Var "x") (toTerm 'b')))
                                   (toTerm ['a', 'b'])
    let alternativesFailInnerGoal = Alternatives (toTerm (Var "x" :: Var Char))
                                                 Bottom
                                                 (toTerm $ Var "xs")
    let alternativesFailInnerTrace = do
          traceCall alternativesFailInnerGoal
          traceCall Bottom
          traceFail Bottom
          traceExit $ Alternatives (toTerm (Var "x" :: Var Char)) Bottom (List Nil)
    let alternativesFailGoal = Alternatives (toTerm (Var "x" :: Var Char)) Top (List Nil)
    let alternativesFailTrace = do
          traceCall alternativesFailGoal
          traceCall Top
          traceExit Top
          traceFail alternativesFailGoal
    let onceGoal = Once $ Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                             (CanUnify (toTerm $ Var "x") (toTerm 'b'))
    let onceTrace = do
          traceCall onceGoal
          traceCall $ Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                         (CanUnify (toTerm $ Var "x") (toTerm 'b'))
          traceCall $ CanUnify (toTerm $ Var "x") (toTerm 'a')
          traceExit $ CanUnify (toTerm 'a') (toTerm 'a')
          traceExit $ Or (CanUnify (toTerm 'a') (toTerm 'a'))
                         (CanUnify (toTerm $ Var "x") (toTerm 'b'))
          traceExit $ Once $ Or (CanUnify (toTerm 'a') (toTerm 'a'))
                                (CanUnify (toTerm $ Var "x") (toTerm 'b'))
    let onceFailGoal = Once Bottom
    let onceFailTrace = do
          traceCall onceFailGoal
          traceCall Bottom
          traceFail Bottom
          traceFail onceFailGoal

    let cutGoal = Or Cut Top
    let cutTrace = do
          traceCall cutGoal
          traceCall Cut
          traceExit Cut
          traceExit cutGoal
    let run g = runTest g (replicate 999 "step")

    it "should prompt after every step of computation" $ do
      run deepGoal deepTrace
      run wideGoal wideTrace
      run backtrackingGoal backtrackingTrace
      run canUnifyGoal canUnifyTrace
      run canUnifyFailGoal canUnifyFailTrace
      run identicalGoal identicalTrace
      run identicalFailGoal identicalFailTrace
      run equalGoal equalTrace
      run equalFailGoal equalFailTrace
      run lessThanGoal lessThanTrace
      run lessThanFailGoal lessThanFailTrace
      run isUnifiedGoal isUnifiedTrace
      run isUnifiedFailGoal isUnifiedFailTrace
      run isVariableGoal isVariableTrace
      run isVariableFailGoal isVariableFailTrace
      run notGoal notTrace
      run notFailGoal notFailTrace
      run andGoal andTrace
      run andFailLeftGoal andFailLeftTrace
      run andFailRightGoal andFailRightTrace
      run orLeftGoal orLeftTrace
      run orRightGoal orRightTrace
      run orFailGoal orFailTrace
      run Top $ traceCall Top >> traceExit Top
      run Bottom $ traceCall Bottom >> traceFail Bottom
      run alternativesGoal alternativesTrace
      run alternativesFailInnerGoal alternativesFailInnerTrace
      run alternativesFailGoal alternativesFailTrace
      run onceGoal onceTrace
      run onceFailGoal onceFailTrace
      run cutGoal cutTrace

  describe "the next command" $ do
    it "should skip to the next event at the current depth" $ do
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["next", "next"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) deep
        traceExit $ PredGoal (predicate "deep" 'a') deep
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide) ["next", "next"] $ do
        traceCall (PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        traceExit (PredGoal (predicate "wide" ('a', 'b', 'c')) wide)
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["step", "next", "next", "next", "next", "next", "next", "next"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide
          traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          traceExit $ PredGoal (predicate "foo" 'a') []
          traceCall $ PredGoal (predicate "bar" (Var "y" :: Var Char)) []
          traceExit $ PredGoal (predicate "bar" 'b') []
          traceCall $ PredGoal (predicate "baz" (Var "z" :: Var Char)) []
          traceExit $ PredGoal (predicate "baz" 'c') []
          traceExit $ PredGoal (predicate "wide" ('a', 'b', 'c')) wide
    it "if no more events at the current depth, it should stop at the next decrease in depth" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["step", "next", "next", "next"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
        traceExit $ PredGoal (predicate "foo" 'a') []
        traceExit $ PredGoal (predicate "deep" 'a') []

  describe "the finish command" $
    it "should skip to the next decrease in depth" $ do
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["step", "finish", "step"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
          setDepth 1 >> traceExit (PredGoal (predicate "wide" ('a', 'b', 'c')) [])
      runTest (PredGoal (predicate "foo" (Var "x" :: Var Char)) backtracking) ["step", "finish", "finish"] $ do
        traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "bar" (Var "x" :: Var Char)) []
        setDepth 1 >> traceFail (PredGoal (predicate "foo" (Var "x" :: Var Char)) [])

  describe "the break/continue commands" $ do
    it "should continue to the next breakpoint" $
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b bar", "b baz", "c", "c", "c"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on bar."
          traceInfo "Set breakpoint on baz."
          setDepth 2 >> traceCall (PredGoal (predicate "bar" (Var "y" :: Var Char)) [])
          setDepth 2 >> traceCall (PredGoal (predicate "baz" (Var "z" :: Var Char)) [])
    it "should warn when the breakpoint already exists" $
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b bar", "b bar", "f"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on bar."
          traceInfo "Breakpoint bar already exists."
  describe "the delete-breakpoint command" $ do
    it "should accept the name of a breakpoint" $
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b bar", "db bar", "c"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on bar."
          traceInfo "Deleted breakpoint bar."
    it "should warn when given a name that does not exist" $
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["db bar", "c"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "No breakpoint \"bar\"."
    it "should accept the index of a breakpoint" $ do
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b bar", "b baz", "db 1", "c", "c"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on bar."
          traceInfo "Set breakpoint on baz."
          traceInfo "Deleted breakpoint bar."
          traceCall $ PredGoal (predicate "baz" (Var "z" :: Var Char)) []
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b bar", "b baz", "db 2", "c", "c"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on bar."
          traceInfo "Set breakpoint on baz."
          traceInfo "Deleted breakpoint baz."
          traceCall $ PredGoal (predicate "bar" (Var "y" :: Var Char)) []
    withParams ["-1", "0", "2"] $ \index ->
      it "should warn when given an out of range" $
        runTest (PredGoal (predicate "wide"
                  (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
          ["b bar", "db " ++ index, "c", "c"] $ do
            traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
            traceInfo "Set breakpoint on bar."
            traceInfo "Index out of range."
            traceCall $ PredGoal (predicate "bar" (Var "y" :: Var Char)) []
  describe "the breakpoints command" $ do
    it "should list active breakpoints" $
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b bar", "b baz", "bs", "c", "c", "c"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on bar."
          traceInfo "Set breakpoint on baz."
          traceInfoLines ["(1) bar", "(2) baz"]
          setDepth 2 >> traceCall (PredGoal (predicate "bar" (Var "y" :: Var Char)) [])
          setDepth 2 >> traceCall (PredGoal (predicate "baz" (Var "z" :: Var Char)) [])
    it "should update to reflect deletions" $
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["b foo", "b bar", "b baz", "db bar", "bs", "f"] $ do
          traceCall $ PredGoal (predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) []
          traceInfo "Set breakpoint on foo."
          traceInfo "Set breakpoint on bar."
          traceInfo "Set breakpoint on baz."
          traceInfo "Deleted breakpoint bar."
          traceInfoLines ["(1) foo", "(2) baz"]

  describe "the goals command" $ do
    it "should print the current goal stack" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["s", "s", "goals", "f", "f", "f"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "bar" (Var "x" :: Var Char)) []
        traceInfoLines
          ["(1) " ++ formatGoal (PredGoal (predicate "deep" (Var "x" :: Var Char)) [])
          ,"(2) " ++ formatGoal (PredGoal (predicate "foo" (Var "x" :: Var Char)) [])
          ,"(3) " ++ formatGoal (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])
          ]
        setDepth 2 >> traceExit (PredGoal (predicate "foo" 'a') [])
        traceExit $ PredGoal (predicate "deep" 'a') []
    it "should print the top N goals from the current goal stack" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["s", "s", "goals 2", "f", "f", "f"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "bar" (Var "x" :: Var Char)) []
        traceInfoLines
          ["(2) " ++ formatGoal (PredGoal (predicate "foo" (Var "x" :: Var Char)) [])
          ,"(3) " ++ formatGoal (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])
          ]
        setDepth 2 >> traceExit (PredGoal (predicate "foo" 'a') [])
        traceExit $ PredGoal (predicate "deep" 'a') []
    it "should print the current goal" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["s", "s", "goal", "f", "f", "f"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "foo" (Var "x" :: Var Char)) []
        traceCall $ PredGoal (predicate "bar" (Var "x" :: Var Char)) []
        traceInfo $ "(3) " ++ formatGoal (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])
        setDepth 2 >> traceExit (PredGoal (predicate "foo" 'a') [])
        traceExit $ PredGoal (predicate "deep" 'a') []
    withParams [0, -1] $ \arg ->
      it "should fail when the argument is not a positive integer" $
        runTest Top ["goals " ++ show arg, "f"] $ do
          traceCall Top
          traceInfo "Argument must be positive."

  describe "the help command" $
    it "should print a usage message" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["help", "finish"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceInfo debugHelp

  describe "a blank command" $
    it "should repeat the previous command" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["n", ""] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceExit $ PredGoal (predicate "deep" 'a') []

  describe "an unknown command" $
    it "should trigger a retry prompt" $ do
      let unexpected = newErrorMessage (UnExpect "\"o\"") (newPos "" 1 2)
      let err = addErrorMessage (Expect "command") unexpected
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep) ["bogus", "finish"] $ do
        traceCall $ PredGoal (predicate "deep" (Var "x" :: Var Char)) []
        traceLines [show err, "Try \"?\" for help."]

  describe "an uninstantiated variables error" $
    it "should print the goal stack" $ do
      let goal = PredGoal (predicate "foo" (Var "x" :: Var Char))
                          [HornClause (predicate "foo" (Var "x" :: Var Char))
                                      (Equal (toTerm 'a') (toTerm (Var "x")))]
      let msg = "Variables are not sufficiently instantiated.\n" ++
                "Goal stack:\n" ++
                "(1) " ++ formatGoal (PredGoal (predicate "foo" (Var "x" :: Var Char)) []) ++ "\n" ++
                "(2) " ++ formatGoal (Equal (toTerm 'a') (toTerm (Var "x")))
      assertError msg $ runTest goal ["n", "n"] (trace "")
