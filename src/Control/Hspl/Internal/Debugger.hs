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
import           Data.Typeable
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

-- | A 'SolverCont' continuation that also maintains a stack of current goals.
debugCont :: Program -> [Goal] -> SolverCont (StateT DebugState IO)
debugCont program stack = SolverCont { tryPredicate = debugFirstAlternative program stack
                                     , retryPredicate = debugNextAlternative program stack
                                     , tryUnifiable = debugUnifiable program stack
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

-- | Get the result that follows from a proof.
getTheorem :: ProofResult -> Goal
getTheorem (Proof g _, _) = g
getTheorem (Axiom g, _) = g

-- | Continuation hook for proving a predicate which matches a given clause.
debugPredicate :: MsgType -> Program -> [Goal] -> Predicate -> HornClause -> Debugger ProofResult
debugPredicate mtype program s p c = do
  let stack = PredGoal p : s
  ifTarget stack $ prompt stack mtype $ show p
  ifte (provePredicateWith (debugCont program stack) program p c)
    (\result -> ifTarget stack (prompt stack Exit (show $ getTheorem result)) >> return result)
    (ifTarget stack (prompt stack Fail $ show p) >> mzero)

-- | Continuation hook for trying the first alternative clause which matches the goal.
debugFirstAlternative :: Program -> [Goal] -> Predicate -> HornClause -> Debugger ProofResult
debugFirstAlternative = debugPredicate Call

-- | Continuation hook for trying additional alternative clauses which match the goal.
debugNextAlternative :: Program -> [Goal] -> Predicate -> HornClause -> Debugger ProofResult
debugNextAlternative = debugPredicate Redo

-- | Continaution hook for proving a 'CanUnify' goal.
debugUnifiable :: Typeable a => Program -> [Goal] -> Term a -> Term a -> Debugger ProofResult
debugUnifiable program s t1 t2 = do
  let stack = CanUnify t1 t2 : s
  ifTarget stack $ prompt stack Call $ show (head stack)
  ifte (proveUnifiableWith (debugCont program stack) program t1 t2)
    (\result -> ifTarget stack (prompt stack Exit (show $ getTheorem result)) >> return result)
    (ifTarget stack (prompt stack Fail $ show (CanUnify t1 t2)) >> mzero)

-- | Continuation hook invoked when a goal with no matching clauses is encountered.
debugErrorUnknownPred :: [Goal] -> Predicate -> Debugger a
debugErrorUnknownPred s p@(Predicate name _) = do
  let stack = PredGoal p : s
  -- Since there are no clauses, there will be no corresponding 'Call' message, rather we will fail
  -- immediately. To make the output a little more intuitive, we explicitly log a 'Call' here.
  ifTarget stack $ prompt stack Call $ show (head stack)
  ifTarget stack $ prompt stack Error $
    "Unknown predicate \"" ++ name ++ " :: " ++ show (predType p) ++ "\""
  mzero

-- | Run the debugger with the given configuration on the given program with the given goal. The
-- result of this function is a computaion in the 'IO' monad which, when executed, will run the
-- debugger.
debug :: DebugConfig -> Program -> Predicate -> IO [ProofResult]
debug config p g = do
  inputH <- if inputFile config == "stdin"
              then return stdin
              else openFile (inputFile config) ReadMode
  outputH <- if outputFile config == "stdout"
              then return stdout
              else openFile (outputFile config) WriteMode
  let st = observeAllSolverT $ proveWith (debugCont p []) p (PredGoal g)
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
unsafeDebug :: Program -> Predicate -> [ProofResult]
unsafeDebug p g = unsafePerformIO $ debug debugConfig p g
