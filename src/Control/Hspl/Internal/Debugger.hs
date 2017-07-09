{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_HADDOCK show-extensions #-}

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
  , debugHelp
  , parseCommand
  , getCommand
  , runCommand
  , repl
  , prompt
  -- * State
  , MsgType (..)
  , Target (..)
  , DebugContext (..)
  , TerminalState (..)
  , initTerminalState
  , closeTerminalState
  -- * Control flow
  -- | The complete debugger is composed of two cooperating coroutines. One routine controls the
  -- interactive terminal. It prompts the user for commands, processes them, and displays the output
  -- to the user. Whenever the user enters a command which should cause exectution to continue (e.g.
  -- 'Step' or 'Next') the terminal routine yields control to the second coroutine.
  --
  -- The second coroutine runs the HSPL solver, attempting to produce a proof of the given goal. At
  -- each step of the computation (e.g. calling a subgoal or returning from a proof) the solver
  -- yields control back to the terminal coroutine and passes it some context about the current
  -- state of the computation. The terminal then decides whether to prompt the user or to continue
  -- the solve.
  , DebugStateT
  , runDebugStateT
  , TerminalCoroutine
  , terminalCoroutine
  , SolverCoroutine
  , solverCoroutine
  , DebugSolverT
  , DebugCont
  -- * Entry points
  , debug
  , unsafeDebug
  ) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative hiding ((<|>))
#endif
import           Control.Monad.Coroutine
import           Control.Monad.Coroutine.SuspensionFunctors hiding (yield)
import qualified Control.Monad.Coroutine.SuspensionFunctors as CR
import           Control.Monad.Identity
import           Control.Monad.Logic
import           Control.Monad.State
import           Data.List
import           Data.Maybe
import           System.Console.ANSI
import           System.IO
import           System.IO.Unsafe
import           Text.Parsec hiding (Error)

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

-- | Initialize the state which will be maintained by 'TerminalCoroutine'. Depending on the
-- configuration, this may include opening file handles, and so the computation must take place in
-- the 'IO' monad.
initTerminalState :: MonadIO m => DebugConfig -> m TerminalState
initTerminalState config = do
  inputH <- if inputFile config == "stdin"
              then return stdin
              else liftIO $ openFile (inputFile config) ReadMode
  outputH <- if outputFile config == "stdout"
              then return stdout
              else liftIO $ openFile (outputFile config) WriteMode
  return Terminal { currentTarget = Any
                  , lastCommand = Step
                  , input = inputH
                  , output = outputH
                  , tty = interactive config
                  , useColors = coloredOutput config
                  }

-- | Clean up any state which must be disposed after the termination of a 'TerminalCoroutine'. For
-- example, input and output file handles which were opened in 'initTerminalState' will be closed.
closeTerminalState :: MonadIO m => DebugConfig -> TerminalState -> m ()
closeTerminalState config st = do
  unless (inputFile config == "stdin") $ liftIO $ hClose $ input st
  unless (outputFile config == "stdout") $ liftIO $ hClose $ output st

-- | The available debugger commands.
data Command =
    -- | Continue execution until the next event (predicate call, failure, or exit).
    Step
    -- | Continue execution until the next event involving the current goal, skipping past any
    -- subgoals.
  | Next
    -- | Continue execution until the next event in the parent goal.
  | Finish
    -- | Print a usage message.
  | Help
  deriving (Show, Eq)

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

-- | Description of the current status of an HSPL computation.
data DebugContext = DC {
                         -- | The current 'Goal' stack. During a computation, this stack will always
                         -- be nonempty. The front of the stack is the 'Goal' currently being worked
                         -- on; the back of the stack is the top-level 'Goal' specified by the user
                         -- who invoked the debugger.
                         stack :: [Goal]
                         -- | The type of event which triggered this context dump.
                       , status :: MsgType
                         -- | Some arbitrary text associated with the event.
                       , msg :: String
                       }

-- | State maintained by the debugger during execution.
data TerminalState = Terminal {
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

-- | Monad transformer which encapsulates the state required by the interactive terminal.
type DebugStateT = StateT TerminalState

-- | Evaluate a compuation in the 'DebugStateT' monad, returning a computation in the underlying
-- monad. The initial state is derived from the given 'DebugConfig'.
runDebugStateT :: MonadIO m => DebugConfig -> DebugStateT m a -> m a
runDebugStateT config m = do
  st <- initTerminalState config
  result <- evalStateT m st
  closeTerminalState config st
  return result

-- | Monad transformer which runs the interactive debugger terminal. It maintains some state, and
-- performs computations in the 'IO' monad. At certain times, it yields control to the calling
-- routine, which should run one step of the computation and then pass control back to the terminal,
-- along with some context about the current state of the computation.
type TerminalCoroutine m = Coroutine (Await (Maybe DebugContext)) (DebugStateT m)

-- | Monad transformer which runs an HSPL program, yielding control and context at each important
-- step of the computation.
type SolverCoroutine m = Coroutine (Yield DebugContext) m

-- | Monad transformer which, when executed using 'observeAllSolverT' or 'observeManySolverT',
-- yields a 'SolverCoroutine'.
type DebugSolverT m = SolverT (SolverCoroutine m)

-- | Suspend a 'SolverCoroutine' with the given context.
yield :: Monad m => DebugContext -> DebugSolverT m ()
yield dc = solverLift $ CR.yield dc

-- | Instance of the 'SolverCont' continuation structure which uses a 'SolverCoroutine' as the
-- underlying monad.
type DebugCont m = SolverCont (SolverCoroutine m)

-- | Continuation functions which run the debugger one step at a time, yielding control and context
-- at each important event.
debugCont :: Monad m => [Goal] -> DebugCont m
debugCont s = SolverCont { tryPredicate = debugFirstAlternative s
                         , retryPredicate = debugNextAlternative s
                         , tryUnifiable = debugUnifiable s
                         , tryIdentical = debugIdentical s
                         , tryEqual = debugEqual s
                         , tryLessThan = debugLessThan s
                         , tryNot = debugNot s
                         , tryAnd = debugAnd s
                         , tryOrLeft = debugOrLeft s
                         , tryOrRight = debugOrRight s
                         , tryTop = debugTop s
                         , tryBottom = debugBottom s
                         , tryAlternatives = debugAlternatives s
                         , failUnknownPred = debugFailUnknownPred s
                         , errorUninstantiatedVariables = debugErrorUninstantiatedVariables s
                         }

-- | Print a line to the 'output' 'Handle'. The end-of-line character depends on whether we are
-- running in interactive mode (i.e. whether 'tty' is set). In interactive mode, the end of line is
-- a ' ', and the user is prompted for input at the end of the same line. In non-interactive mode,
-- each line of output is terminated by a '\n' character.
printLine :: MonadIO m => String -> TerminalCoroutine m ()
printLine s = do
  st <- lift get
  let endChar = if tty st then " " else "\n"
  liftIO $ hPutStr (output st) $ s ++ endChar

-- | Read a 'Command' from a string. This accounts for short aliases of commands. For example,
--
-- >>> parseCommand "step"
-- Just Step
--
-- >>> parseCommand "s"
-- Just Step
parseCommand :: MonadIO m => String -> TerminalCoroutine m (Either ParseError Command)
parseCommand str = do
  st <- lift get

  let tok t = try $ spaces *> string t <* spaces
      step = (tok "step" <|> tok "s") >> return Step
      next = (tok "next" <|> tok "n") >> return Next
      finish = (tok "finish" <|> tok "f") >> return Finish
      help = (tok "help" <|> tok "h" <|> tok "?") >> return Help
      repeatLast = tok "" >> return (lastCommand st)
      command = step <|> next <|> finish <|> help <|> repeatLast

  return $ parse (spaces *> command <* spaces <* eof <?> "command") "" str

-- | Read a 'Command' from the input file handle. If the input is not a valid command, an error
-- message is shown and the user is prompted to re-enter the command. This loop continues until a
-- valid command is entered.
getCommand :: MonadIO m => TerminalCoroutine m Command
getCommand = do
  st <- lift get
  commStr <- liftIO $ hGetLine $ input st
  comm <- parseCommand commStr
  case comm of
    Left err -> printLine (show err ++ "\nTry \"?\" for help.") >> getCommand
    Right c -> return c

-- | Process a 'Command'. When this function returns, the command will be stored in 'lastCommand',
-- and 'currentTarget' will be set appropriately. The return value indicates whether the processed
-- command should cause the solver to continue executing. For example, if the given command is
-- 'Next', the return value will be 'True', and the caller should thus yield control back to the
-- solver. But if the given command is, say, 'Help', the caller should simply prompt for another
-- command.
runCommand :: MonadIO m => DebugContext -> Command -> TerminalCoroutine m Bool
runCommand DC { stack = s } c = do
  st <- lift get
  result <- case c of
    Step -> lift (put st { currentTarget = Any }) >> return True
    Next -> lift (put st { currentTarget = Depth $ length s }) >> return True
    Finish -> lift (put st { currentTarget = Depth $ length s - 1 }) >> return True
    Help -> printLine debugHelp >> return False

  lift $ modify $ \st' -> st' { lastCommand = c }

  return result

-- | Read and evalute commands until a command is entered which causes control to be yielded back to
-- the solver.
repl :: (Functor m, MonadIO m) => DebugContext -> TerminalCoroutine m ()
repl context = do
  c <- getCommand
  shouldYield <- runCommand context c
  unless shouldYield $ repl context

-- | Entry point when yielding control from the solver to the terminal. This function outputs a
-- message to the user based on the yielded context, and then enters the interactive 'repl'.
prompt :: (Functor m, MonadIO m) => DebugContext -> TerminalCoroutine m ()
prompt context@DC { stack = s, status = mtype, msg = m } = do
  st <- lift get
  let shouldStop = case currentTarget st of
                      Any -> True
                      Depth d -> length s <= d
  when shouldStop $ do
    liftIO $ hPutStr (output st) $ "(" ++ show (length s) ++ ") "
    liftIO $ setSGR [msgColor mtype | useColors st]
    liftIO $ hPutStr (output st) $ show mtype ++ ": "
    liftIO $ setSGR []
    printLine m
    repl context

-- | Same as callWith, but for unitary provers.
callWith0 :: Monad m => MsgType -> [Goal] -> (DebugCont m -> DebugSolverT m ProofResult) ->
                        DebugSolverT m ProofResult
callWith0 m s cont = do
  let dc = DC { stack = s, status = m, msg = show (head s) }
  yield dc
  ifte (cont $ debugCont s)
    (\result -> yield dc { status = Exit, msg = show (getSolution result) } >> return result)
    (yield dc { status = Fail } >> mzero)

-- | Attempt to prove a subgoal, logging a message of the given type on entry and either 'Exit' or
-- 'Fail' as appropriate.
callWith :: Monad m => MsgType -> [Goal] -> (DebugCont m -> a -> DebugSolverT m ProofResult) ->
            a -> DebugSolverT m ProofResult
callWith m s cont g = callWith0 m s (\c -> cont c g)

-- | Same as call, but for 2-ary provers.
callWith2 :: Monad m => MsgType -> [Goal] -> (DebugCont m -> a -> b -> DebugSolverT m ProofResult) ->
                        a -> b -> DebugSolverT m ProofResult
callWith2 m s cont a b = callWith m s (\c (x, y) -> cont c x y) (a, b)

-- | Same as call, but for 3-ary provers.
callWith3 :: Monad m => MsgType -> [Goal] ->
                        (DebugCont m -> a -> b -> c -> DebugSolverT m ProofResult) ->
                        a -> b -> c -> DebugSolverT m ProofResult
callWith3 m s cont a b c = callWith m s (\cont' (x, y, z) -> cont cont' x y z) (a, b, c)

-- | Attempt to prove a subgoal and log 'Call', 'Exit', and 'Fail' messages as appropriate.
call :: Monad m =>
        [Goal] -> (DebugCont m -> a -> DebugSolverT m ProofResult) -> a -> DebugSolverT m ProofResult
call = callWith Call

-- | Same as call, but for 2-ary provers.
call2 :: Monad m => [Goal] -> (DebugCont m -> a -> b -> DebugSolverT m ProofResult) ->
                    a -> b -> DebugSolverT m ProofResult
call2 = callWith2 Call

-- | Same as call, but for 3-ary provers.
call3 :: Monad m => [Goal] -> (DebugCont m -> a -> b -> c -> DebugSolverT m ProofResult) ->
                    a -> b -> c -> DebugSolverT m ProofResult
call3 = callWith3 Call

-- | Same as call, but for unitary provers.
call0 :: Monad m => [Goal] -> (DebugCont m -> DebugSolverT m ProofResult) -> DebugSolverT m ProofResult
call0 = callWith0 Call

-- | Continuation hook for trying the first alternative clause which matches the goal.
debugFirstAlternative :: Monad m => [Goal] -> Predicate -> HornClause -> DebugSolverT m ProofResult
debugFirstAlternative s p c =
  let s' = PredGoal p [] : s
  in callWith2 Call s' provePredicateWith p c

-- | Continuation hook for trying additional alternative clauses which match the goal.
debugNextAlternative :: Monad m => [Goal] -> Predicate -> HornClause -> DebugSolverT m ProofResult
debugNextAlternative s p c =
  let s' = PredGoal p [] : s
  in callWith2 Redo s' provePredicateWith p c

-- | Continaution hook for proving a 'CanUnify' goal.
debugUnifiable :: (Monad m, TermEntry a) => [Goal] -> Term a -> Term a -> DebugSolverT m ProofResult
debugUnifiable s t1 t2 =
  let s' = CanUnify t1 t2 : s
  in call2 s' proveUnifiableWith t1 t2

-- | Continaution hook for proving an 'Identical' goal.
debugIdentical :: (Monad m, TermEntry a) => [Goal] -> Term a -> Term a -> DebugSolverT m ProofResult
debugIdentical s t1 t2 =
  let s' = Identical t1 t2 : s
  in call2 s' proveIdenticalWith t1 t2

-- | Continuation hook for proving an 'Equal' goal.
debugEqual :: (Monad m, TermEntry a) => [Goal] -> Term a -> Term a -> DebugSolverT m ProofResult
debugEqual s lhs rhs =
  let s' = Equal lhs rhs : s
  in call2 s' proveEqualWith lhs rhs

-- | Continuation hook for proving a 'LessThan' goal.
debugLessThan :: (Monad m, TermEntry a, Ord a) =>
                 [Goal] -> Term a -> Term a -> DebugSolverT m ProofResult
debugLessThan s lhs rhs =
  let s' = LessThan lhs rhs : s
  in call2 s' proveLessThanWith lhs rhs

-- | Continuation hook for proving a 'Not' goal.
debugNot :: Monad m => [Goal] -> Goal -> DebugSolverT m ProofResult
debugNot s g =
  let s' = Not g : s
  in call s' proveNotWith g

debugAnd :: Monad m => [Goal] -> Goal -> Goal -> DebugSolverT m ProofResult
-- No 'call' here, we don't trace the 'And' itself. To the user, proving a conjunction just loooks
-- like proving each subgoal in sequence.
debugAnd s = proveAndWith (debugCont s)

-- | Continuation hook for proving one branch of an 'Or' goal.
debugOrLeft :: Monad m => [Goal] -> Goal -> Goal -> DebugSolverT m ProofResult
debugOrLeft s g1 g2 =
  let s' = Or g1 g2 : s
  in call2 s' proveOrLeftWith g1 g2

debugOrRight :: Monad m => [Goal] -> Goal -> Goal -> DebugSolverT m ProofResult
debugOrRight s g1 g2 =
  let s' = Or g1 g2 : s
  in callWith2 Redo s' proveOrRightWith g1 g2

debugTop :: Monad m => [Goal] -> DebugSolverT m ProofResult
debugTop s =
  let s' = Top : s
  in call0 s' proveTopWith

debugBottom :: Monad m => [Goal] -> DebugSolverT m ProofResult
debugBottom s =
  let s' = Bottom : s
  in call0 s' proveBottomWith

debugAlternatives :: (Monad m, TermEntry a) =>
                     [Goal] -> Term a -> Goal -> Term [a] -> DebugSolverT m ProofResult
debugAlternatives s x g xs =
  let s' = Alternatives x g xs : s
  in call3 s' proveAlternativesWith x g xs

-- | Continuation hook invoked when a goal with no matching clauses is encountered.
debugFailUnknownPred :: Monad m => [Goal] -> Predicate -> DebugSolverT m ProofResult
debugFailUnknownPred s p@(Predicate name _) = do
  let s' = PredGoal p [] : s
  -- Since there are no clauses, there will be no corresponding 'Call' message, rather we will fail
  -- immediately. To make the output a little more intuitive, we explicitly log a 'Call' here.
  yield DC { stack = s', status = Call, msg = show (head s') }
  yield DC { stack = s'
           , status = Error
           , msg = "Unknown predicate \"" ++ name ++ " :: " ++ show (predType p) ++ "\""
           }
  mzero

-- | Continuation hook resulting in a runtime error when attempting to evaluate a 'Term' containing
-- ununified variables.
debugErrorUninstantiatedVariables :: [Goal] -> a
debugErrorUninstantiatedVariables s =
  let annotatedStack =
        ["(" ++ show d ++ ") " ++ show g | (d, g) <- zip ([1..] :: [Int]) (reverse s)]
  in error $ "Variables are not sufficiently instantiated.\nGoal stack:\n" ++
             intercalate "\n" annotatedStack

-- | A coroutine which controls the HSPL solver, yielding control at every important event.
solverCoroutine :: Monad m => Goal -> SolverCoroutine m [ProofResult]
solverCoroutine g = observeAllSolverT $ proveWith (debugCont []) g

-- | A coroutine which controls the interactive debugger terminal, periodically yielding control to
-- the solver.
terminalCoroutine :: (Functor m, MonadIO m) => TerminalCoroutine m ()
terminalCoroutine = await >>= \mc -> when (isJust mc) $ do
  prompt $ fromJust mc
  terminalCoroutine

-- | Run the debugger with the given configuration and goal. The result of this function is a
-- computaion in the 'IO' monad which, when executed, will run the debugger.
debug :: (Functor m, MonadIO m) => DebugConfig -> Goal -> m [ProofResult]
debug c g =
  let cr = weave sequentialBinder weaveAwaitMaybeYield terminalCoroutine (solverCoroutine g)
      st = pogoStick runIdentity cr
  in fmap snd $ runDebugStateT c st -- Keep the solver output, ignore the terminal output

-- | Immediately run the debugger outside of the 'IO' monad. This function simply passes the result
-- of 'debug' to 'unsafePerformIO'. Because of this, it should never be used in production. The
-- intended use for this function is to import the module containing the HSPL program into a REPL
-- and run 'unsafeDebug' from there.
unsafeDebug :: Goal -> [ProofResult]
unsafeDebug = unsafePerformIO . debug debugConfig
