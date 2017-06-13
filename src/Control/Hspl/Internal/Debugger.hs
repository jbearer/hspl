{-|
Module      : Control.Hspl.Internal.Debugger
Description : An interactive debugger for HSPL programs.
Stability   : Internal

This module implements an interactive debugger for HSPL programs. The debugger hooks into the HSPL
prover using the 'ProverCont' framework, and provides several commands for navigating through an
HSPL program:

* step: continue execution until the next continuation event
* next: continue execution until the next event in the current goal
* finish: continue execution until the next event in the parent goal
-}
module Control.Hspl.Internal.Debugger (
  -- * Configuration
    DebugConfig (..)
  , debugConfig
  -- * Commands
  , Command (..)
  , parseCommand
  , debugHelp
  -- * Debugger
  , MsgType (..)
  , Target (..)
  , DebugState (..)
  , Debugger
  , debug
  , unsafeDebug
  ) where

import           Control.Monad.Logic
import           Control.Monad.State
import qualified Data.Map as M
import           System.Console.ANSI
import           System.IO
import           System.IO.Unsafe

import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Solver

-- | Structure used to specify configuration options for the debugger.
data DebugConfig = DebugConfig {
                                 -- | File from which to read input commands. If this is the special
                                 -- string "stdin", then commands are read from standard input.
                                 -- Otherwise, this is treated as a file path and opened in read-
                                 -- only mode.
                                 inputFile :: FilePath
                                 -- | File to which to write debugger output. If this is the special
                                 -- string "stdout", then output is written to standard output.
                                 -- Otherwise, this is treated as a file path and opened in write-
                                 -- only mode.
                               , outputFile :: FilePath
                                 -- | Specifies whether the debugger should run in interactive mode.
                               , interactive :: Bool
                                 -- | Specifies whether the debugger should color-code its output.
                                 -- Should only be used when @outputFile == "stdout"@ and stdout is
                                 -- a terminal.
                               , coloredOutput :: Bool
                               }

-- | Sane default values for a 'DebugConfig' which set up the debugger for interactive use at a
-- terminal.
debugConfig :: DebugConfig
debugConfig = DebugConfig { inputFile = "stdin"
                          , outputFile = "stdout"
                          , interactive = True
                          , coloredOutput = True
                          }

-- | The available debugger commands.
data Command =
    -- | Continue execution until the next event (predicate call, failure, or exit).
    Step
    -- | Continue execution until the next event involving the current goal, skipping past any
    -- subgoals.
  | Next
    -- | Continue execution until the next event in the parent goal.
  | Finish

-- | Read a 'Command' from a string. This accounts for short aliases of commands. For example,
--
-- >>> parseCommand "step"
-- Just Step
--
-- >>> parseCommand "s"
-- Just Step
parseCommand :: String -> Maybe Command
parseCommand s = M.lookup s $ M.fromList [ ("s", Step), ("step", Step)
                                         , ("n", Next), ("next", Next)
                                         , ("f", Finish), ("finish", Finish)
                                         ]

-- | A usage message describing the various commands offered by the debugger.
debugHelp :: String
debugHelp = unlines ["s, step: proceed one predicate call"
                    ,"n, next: proceed to the next call, failure, or exit at this level"
                    ,"f, finish: proceed to the exit or failure of the current goal"
                    ,"?, h, help: show this help"
                    , "<return>: replay last command"
                    ]

-- | Descriptor of the next event at which to stop execution and prompt the user for a command.
data Target =
    -- | Stop at any event with debug hooks
    Any
    -- | Stop at an event occuring at a depth less than or equal to the specified depth.
  | Depth Int

-- | The various events which trigger debug messages.
data MsgType = Call | Redo | Exit | Fail | Error
  deriving (Show)

-- | Mapping from events ('MsgType') to 'SGR' commands which set the console color.
msgColor :: MsgType -> SGR
msgColor Call = SetColor Foreground Vivid Green
msgColor Redo = SetColor Foreground Vivid Yellow
msgColor Exit = SetColor Foreground Vivid Green
msgColor Fail = SetColor Foreground Vivid Red
msgColor Error = SetColor Foreground Vivid Red

-- | State maintained by the debugger during execution.
data DebugState = DS {
                       -- | Descriptor of the next event at which to stop execution and prompt the
                       -- user for a command.
                       currentTarget :: Target
                       -- | The last command issued by the user.
                     , lastCommand :: Command
                       -- | File 'Handle' from which to read commands.
                     , input :: Handle
                       -- | File 'Handle' to which to print output.
                     , output :: Handle
                       -- | Whether 'output' is a terminal.
                     , tty :: Bool
                       -- | Whether output should be color-coded.
                     , useColors :: Bool
                     }

-- | Monad which encapsulates the 'DebugState' during execution.
type Debugger = SolverT (StateT DebugState IO)

type DebugCont = SolverCont (StateT DebugState IO)

-- | A 'SolverCont' continuation that also maintains a stack of current goals.
debugCont :: [Goal] -> DebugCont
debugCont stack = SolverCont { tryPredicate = debugFirstAlternative stack
                             , retryPredicate = debugNextAlternative stack
                             , tryUnifiable = debugUnifiable stack
                             , tryIdentical = debugIdentical stack
                             , tryEqual = debugEqual stack
                             , tryNot = debugNot stack
                             , tryAnd = debugAnd stack
                             , tryOrLeft = debugOrLeft stack
                             , tryOrRight = debugOrRight stack
                             , tryTop = debugTop stack
                             , tryBottom = debugBottom stack
                             , errorUnknownPred = debugErrorUnknownPred stack
                             }

-- | Print a line to the 'output' 'Handle'. The end-of-line character depends on whether we are
-- running in interactive mode (i.e. whether 'tty' is set). In interactive mode, the end of line is
-- a ' ', and the user is prompted for input at the end of the same line. In non-interactive mode,
-- each line of output is terminated by a '\n' character.
printLine :: String -> Debugger ()
printLine s = do
  st <- solverLift get
  let endChar = if tty st then " " else "\n"
  liftIO $ hPutStr (output st) $ s ++ endChar

-- | Read a command from 'input'.
getCommand :: Debugger Command
getCommand = do
  st <- solverLift get
  comm <- liftIO $ hGetLine $ input st
  if comm == "" then
    fmap lastCommand $ solverLift get
  else if comm == "?" || comm == "h" || comm == "help" then
    printLine debugHelp >> getCommand
  else case parseCommand comm of
    Just c -> return c
    Nothing -> printLine ("Unknown command \"" ++ comm ++ "\". Try \"?\" for help.") >> getCommand

-- | Display a message to the user and wait for the next command. When this function returns, the
-- command will be stored in 'lastCommand', and 'currentTarget' will be set appropriately.
prompt :: [Goal] -> MsgType -> String -> Debugger ()
prompt stack mtype msg = do
  st <- solverLift get
  liftIO $ hPutStr (output st) $ "(" ++ show (length stack) ++ ") "
  liftIO $ setSGR [msgColor mtype | useColors st]
  liftIO $ hPutStr (output st) $ show mtype ++ ": "
  liftIO $ setSGR []
  printLine msg
  comm <- getCommand
  let nextTarget = case comm of
                    Step -> Any
                    Next -> Depth (length stack)
                    Finish -> Depth $ length stack - 1
  solverLift $ put st { currentTarget = nextTarget, lastCommand = comm }

-- | Determine whether we should stop and prompt the user.
ifTarget :: [Goal] -> Debugger () -> Debugger ()
ifTarget stack m = do
  st <- solverLift get
  case currentTarget st of
    Any -> m
    Depth d | length stack <= d -> m
    _ -> return ()

-- | Same as callWith, but for unitary provers.
callWith0 :: MsgType -> [Goal] -> (DebugCont -> Debugger ProofResult) -> Debugger ProofResult
callWith0 msg stack cont = do
  ifTarget stack $ prompt stack msg $ show (head stack)
  ifte (cont $ debugCont stack)
    (\result -> ifTarget stack (prompt stack Exit (show $ getSolution result)) >> return result)
    (ifTarget stack (prompt stack Fail $ show (head stack)) >> mzero)

-- | Attempt to prove a subgoal, logging a message of the given type on entry and either 'Exit' or
-- 'Fail' as appropriate.
callWith :: MsgType -> [Goal] -> (DebugCont -> a -> Debugger ProofResult) -> a -> Debugger ProofResult
callWith msg stack cont g = callWith0 msg stack (\c -> cont c g)

-- | Same as call, but for 2-ary provers.
callWith2 :: MsgType -> [Goal] -> (DebugCont -> a -> b -> Debugger ProofResult) -> a -> b -> Debugger ProofResult
callWith2 msg stack cont a b = callWith msg stack (\c (x, y) -> cont c x y) (a, b)

-- | Attempt to prove a subgoal and log 'Call', 'Exit', and 'Fail' messages as appropriate.
call :: [Goal] -> (DebugCont -> a -> Debugger ProofResult) -> a -> Debugger ProofResult
call = callWith Call

-- | Same as call, but for 2-ary provers.
call2 :: [Goal] -> (DebugCont -> a -> b -> Debugger ProofResult) -> a -> b -> Debugger ProofResult
call2 = callWith2 Call

-- | Same as call, but for unitary provers.
call0 :: [Goal] -> (DebugCont -> Debugger ProofResult) -> Debugger ProofResult
call0 = callWith0 Call

-- | Continuation hook for trying the first alternative clause which matches the goal.
debugFirstAlternative :: [Goal] -> Predicate -> HornClause -> Debugger ProofResult
debugFirstAlternative s p c =
  let stack = PredGoal p [] : s
  in callWith2 Call stack provePredicateWith p c

-- | Continuation hook for trying additional alternative clauses which match the goal.
debugNextAlternative :: [Goal] -> Predicate -> HornClause -> Debugger ProofResult
debugNextAlternative s p c =
  let stack = PredGoal p [] : s
  in callWith2 Redo stack provePredicateWith p c

-- | Continaution hook for proving a 'CanUnify' goal.
debugUnifiable :: TermEntry a => [Goal] -> Term a -> Term a -> Debugger ProofResult
debugUnifiable s t1 t2 =
  let stack = CanUnify t1 t2 : s
  in call2 stack proveUnifiableWith t1 t2

-- | Continaution hook for proving an 'Identical' goal.
debugIdentical :: TermEntry a => [Goal] -> Term a -> Term a -> Debugger ProofResult
debugIdentical s t1 t2 =
  let stack = Identical t1 t2 : s
  in call2 stack proveIdenticalWith t1 t2

-- | Continuation hook for proving an 'Equal' goal.
debugEqual :: (TermEntry a) => [Goal] -> Term a -> Term a -> Debugger ProofResult
debugEqual s lhs rhs =
  let stack = Equal lhs rhs : s
  in call2 stack proveEqualWith lhs rhs

-- | Continuation hook for proving a 'Not' goal.
debugNot :: [Goal] -> Goal -> Debugger ProofResult
debugNot s g =
  let stack = Not g : s
  in call stack proveNotWith g

debugAnd :: [Goal] -> Goal -> Goal -> Debugger ProofResult
-- No 'call' here, we don't trace the 'And' itself. To the user, proving a conjunction just loooks
-- like proving each subgoal in sequence.
debugAnd s = proveAndWith (debugCont s)

-- | Continuation hook for proving one branch of an 'Or' goal.
debugOrLeft :: [Goal] -> Goal -> Goal -> Debugger ProofResult
debugOrLeft s g1 g2 =
  let stack = Or g1 g2 : s
  in call2 stack proveOrLeftWith g1 g2

debugOrRight :: [Goal] -> Goal -> Goal -> Debugger ProofResult
debugOrRight s g1 g2 =
  let stack = Or g1 g2 : s
  in callWith2 Redo stack proveOrRightWith g1 g2

debugTop :: [Goal] -> Debugger ProofResult
debugTop s =
  let stack = Top : s
  in call0 stack proveTopWith

debugBottom :: [Goal] -> Debugger ProofResult
debugBottom s =
  let stack = Bottom : s
  in call0 stack proveBottomWith

-- | Continuation hook invoked when a goal with no matching clauses is encountered.
debugErrorUnknownPred :: [Goal] -> Predicate -> Debugger a
debugErrorUnknownPred s p@(Predicate name _) = do
  let stack = PredGoal p [] : s
  -- Since there are no clauses, there will be no corresponding 'Call' message, rather we will fail
  -- immediately. To make the output a little more intuitive, we explicitly log a 'Call' here.
  ifTarget stack $ prompt stack Call $ show (head stack)
  ifTarget stack $ prompt stack Error $
    "Unknown predicate \"" ++ name ++ " :: " ++ show (predType p) ++ "\""
  mzero

-- | Run the debugger with the given configuration and goal. The result of this function is a
-- computaion in the 'IO' monad which, when executed, will run the debugger.
debug :: DebugConfig -> Goal -> IO [ProofResult]
debug config g = do
  inputH <- if inputFile config == "stdin"
              then return stdin
              else openFile (inputFile config) ReadMode
  outputH <- if outputFile config == "stdout"
              then return stdout
              else openFile (outputFile config) WriteMode
  let st = observeAllSolverT $ proveWith (debugCont []) g
  results <- evalStateT st DS { currentTarget = Any
                              , lastCommand = Step
                              , input = inputH
                              , output = outputH
                              , tty = interactive config
                              , useColors = coloredOutput config
                              }
  unless (inputFile config == "stdin") $ hClose inputH
  unless (outputFile config == "stdout") $ hClose outputH
  return results

-- | Immediately run the debugger outside of the 'IO' monad. This function simply passes the result
-- of 'debug' to 'unsafePerformIO'. Because of this, it should never be used in production. The
-- intended use for this function is to import the module containing the HSPL program into a REPL
-- and run 'unsafeDebug' from there.
unsafeDebug :: Goal -> [ProofResult]
unsafeDebug = unsafePerformIO . debug debugConfig
