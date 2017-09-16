{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.Debugger
Description : An interactive debugger for HSPL programs.
Stability   : Internal

This module implements an interactive debugger for HSPL programs. The debugger hooks into the HSPL
prover using the 'ProverCont' framework, and provides several commands for navigating through an
HSPL program.
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
  -- , DebugCont
  -- * Entry points
  , debug
  ) where

import           Control.Applicative hiding ((<|>))
import           Control.Exception (finally)
import           Control.Monad.Coroutine
import           Control.Monad.Coroutine.SuspensionFunctors hiding (yield)
import qualified Control.Monad.Coroutine.SuspensionFunctors as CR
import           Control.Monad.Identity
import           Control.Monad.State
import           Data.Char
import           Data.List
import           Data.Maybe
import           System.Console.ANSI
import           System.IO
import           Text.Parsec hiding (Error, tokens)

import Control.Hspl.Internal.Ast hiding (predicate)
import Control.Hspl.Internal.Logic
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.Tuple
import Control.Hspl.Internal.UI
import Control.Hspl.Internal.Unification (MonadVarGenerator, MonadUnification (..), munify)

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
initTerminalState :: DebugConfig -> IO TerminalState
initTerminalState config = do
  inputH <- if inputFile config == "stdin"
              then return stdin
              else openFile (inputFile config) ReadMode
  outputH <- if outputFile config == "stdout"
              then return stdout
              else openFile (outputFile config) WriteMode
  return Terminal { currentTarget = Any
                  , lastCommand = Step
                  , breakpoints = []
                  , input = inputH
                  , output = outputH
                  , tty = interactive config
                  , useColors = coloredOutput config
                  }

-- | Clean up any state which must be disposed after the termination of a 'TerminalCoroutine'. For
-- example, input and output file handles which were opened in 'initTerminalState' will be closed.
closeTerminalState :: DebugConfig -> TerminalState -> IO ()
closeTerminalState config st = do
  unless (inputFile config == "stdin") $ hClose $ input st
  unless (outputFile config == "stdout") $ hClose $ output st

-- | The available debugger commands.
data Command =
    -- | Continue execution until the next event (predicate call, failure, or exit).
    Step
    -- | Continue execution until the next event involving the current goal, skipping past any
    -- subgoals.
  | Next
    -- | Continue execution until the next event in the parent goal.
  | Finish
    -- | Continue execution until the next breakpoint.
  | Continue
    -- | Set a breakpoint on a predicate, specified by name.
  | SetBreakpoint String
    -- | Delete a breakpoint, specified either by name or by the index associated with that
    -- breakpoint in 'InfoBreakpoints'.
  | DeleteBreakpoint (Either String Int)
    -- | Show the currently set breakpoints.
  | InfoBreakpoints
    -- | Print out the current goal stack.
  | InfoStack (Maybe Int)
    -- | Print a usage message.
  | Help
  deriving (Show, Eq)

-- | A usage message describing the various commands offered by the debugger.
debugHelp :: String
debugHelp = unlines
  ["s, step: proceed one predicate call"
  ,"n, next: proceed to the next call, failure, or exit at this level"
  ,"f, finish: proceed to the exit or failure of the current goal"
  ,"c, continue: proceed to the next breakpoint"
  ,"b, break <predicate>: set a breakpoint to stop execution when calling a predicate with the"
  ,"    given name"
  ,"db, delete-breakpoint <breakpoint>: remove a breakpoint previously created via break. The"
  ,"    breakpoint to delete can be specified by the same string passed to break, or by the"
  ,"    breakpoint index listed in breakpoints"
  ,"bs, breakpoints: list currently enabled breakpoints"
  ,"gs, goals [N]: print the most recent N goals from the goal stack, or all goals if no N is given"
  ,"g, goal: print the current goal (equivalent to 'goals 1')"
  ,"?, h, help: show this help"
  , "<return>: replay last command"
  ]

-- | Descriptor of the next event at which to stop execution and prompt the user for a command.
data Target =
    -- | Stop at any event with debug hooks
    Any
    -- | Stop at an event occuring at a depth less than or equal to the specified depth.
  | Depth Int
    -- | Stop when calling a predicate matching a breakpoint
  | Breakpoint

-- | The various events which trigger debug messages.
data MsgType = Call | Redo | Exit | Fail | Error
  deriving (Show, Eq)

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
                       -- | List of predicates which we should stop at when running until a
                       -- breakpoint.
                     , breakpoints :: [String]
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
runDebugStateT :: DebugConfig -> DebugStateT IO a -> IO a
runDebugStateT config m = do
  st <- initTerminalState config
  result <- evalStateT m st `finally` closeTerminalState config st
  return result

-- | Monad which runs the interactive debugger terminal. It maintains some state, and performs
-- computations in the 'IO' monad. At certain times, it yields control to the calling routine, which
-- should run one step of the computation and then pass control back to the terminal, along with
-- some context about the current state of the computation.
type TerminalCoroutine = Coroutine (Await (Maybe DebugContext)) (DebugStateT IO)

-- | Monad transformer which runs an HSPL program, yielding control and context at each important
-- step of the computation.
type SolverCoroutine m = Coroutine (Yield DebugContext) m

-- | State maintained by the solver coroutine.
data SolverState = Solver {
                     -- | The current goal stack. @head goalStack@ is the current goal,
                     -- @goalStack !! 1@ is the parent of that goal, and so on, so that
                     -- @last goalStack@ is the top-level goal we are ultimately trying to prove.
                     goalStack :: [Goal]
                   }

instance SplittableState SolverState where
  type BacktrackingState SolverState = [Goal]
  type GlobalState SolverState = ()
  splitState s = (goalStack s, ())
  combineState gs () = Solver { goalStack = gs }

-- | Monad transformer which, when executed using 'observeAllSolverT' or 'observeManySolverT',
-- yields a 'SolverCoroutine'.
newtype DebugSolverT m a = DebugSolverT { unDebugSolverT :: SolverT SolverState (SolverCoroutine m) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadLogic, MonadLogicCut, MonadVarGenerator, MonadUnification)

-- | Same as callWith, but for unitary provers.
callWith :: Monad m => MsgType -> DebugSolverT m Theorem -> DebugSolverT m Theorem
callWith m cont = do
  s <- gets goalStack
  let dc = DC { stack = s, status = m, msg = formatGoal (head s) }
  yield dc
  ifte cont
    (\thm -> do thm' <- munify thm
                yield dc { status = Exit, msg = formatGoal thm' }
                return thm)
    (yield dc { status = Fail } >> mzero)

-- | Attempt to prove a subgoal and log 'Call', 'Exit', and 'Fail' messages as appropriate.
call :: Monad m => DebugSolverT m Theorem -> DebugSolverT m Theorem
call = callWith Call

-- | Run a 'DebugSolverT' action with the given goal at the top of the goal stack.
goalFrame :: Monad m => Goal -> DebugSolverT m a -> DebugSolverT m a
goalFrame g m = do
  s <- get
  put $ s { goalStack = g : goalStack s }
  r <- m
  put s
  return r

instance MonadTrans DebugSolverT where
  lift = DebugSolverT . lift . lift

instance Monad m => MonadState SolverState (DebugSolverT m) where
  state = DebugSolverT . state

instance Monad m => MonadSolver (DebugSolverT m) where
  recordThm = DebugSolverT . recordThm
  getRecordedThms = DebugSolverT getRecordedThms

  tryPredicate p c = goalFrame (PredGoal p []) (call $ provePredicate p c)
  retryPredicate p c = goalFrame (PredGoal p []) (callWith Redo $ provePredicate p c)
  tryUnifiable t1 t2 = goalFrame (CanUnify t1 t2) (call $ proveUnifiable t1 t2)
  tryIdentical t1 t2 = goalFrame (Identical t1 t2) (call $ proveIdentical t1 t2)
  tryEqual lhs rhs = goalFrame (Equal lhs rhs) (call $ proveEqual lhs rhs)
  tryLessThan lhs rhs = goalFrame (LessThan lhs rhs) (call $ proveLessThan lhs rhs)
  tryIsUnified t = goalFrame (IsUnified t) (call $ proveIsUnified t)
  tryIsVariable t = goalFrame (IsVariable t) (call $ proveIsVariable t)
  tryNot g = goalFrame (Not g) (call $ proveNot g)
  tryAnd = proveAnd -- No 'call' here, we don't trace the 'And' itself. To the user, proving a
                    -- conjunction just looks like proving each subgoal in sequence.
  tryOrLeft g1 g2 = goalFrame (Or g1 g2) (call $ proveOrLeft g1 g2)
  tryOrRight g1 g2 = goalFrame (Or g1 g2) (callWith Redo $ proveOrRight g1 g2)
  tryTop = goalFrame Top (call proveTop)
  tryBottom = goalFrame Bottom (call proveBottom)
  tryAlternatives n x g xs = goalFrame (Alternatives n x g xs) (call $ proveAlternatives n x g xs)
  tryOnce g = goalFrame (Once g) (call $ proveOnce g)
  tryCut = goalFrame Cut (call proveCut)
  tryTrack g = goalFrame (Track g) (call $ proveTrack g)

  failUnknownPred p@(Predicate name _) = do
    s <- gets $ (PredGoal p [] :) . goalStack
    -- Since there are no clauses, there will be no corresponding 'Call' message, rather we will fail
    -- immediately. To make the output a little more intuitive, we explicitly log a 'Call' here.
    yield DC { stack = s, status = Call, msg = formatGoal (head s) }
    yield DC { stack = s
             , status = Error
             , msg = "Unknown predicate \"" ++ name ++ " :: " ++ formatType (predType p) ++ "\""
             }
    mzero

  errorUninstantiatedVariables = gets goalStack >>= \s -> error $
    "Variables are not sufficiently instantiated.\nGoal stack:\n" ++ showStack Nothing s

-- | Suspend a 'SolverCoroutine' with the given context.
yield :: Monad m => DebugContext -> DebugSolverT m ()
yield dc = DebugSolverT $ lift $ CR.yield dc

-- | Format a goal stack in a manner suitable for displaying to the user. If a number @n@ is
-- specified, then just the top @n@ goals are shown from the stack. Otherwise, the entire stack is
-- displayed.
showStack :: Maybe Int -> [Goal] -> String
showStack mn s =
  let enumeratedStack = zip ([1..] :: [Int]) (reverse s)
      truncatedStack = case mn of
                          Just n -> reverse $ take n $ reverse enumeratedStack
                          Nothing -> enumeratedStack
  in intercalate "\n" ["(" ++ show d ++ ") " ++ formatGoal g | (d, g) <- truncatedStack]

showBreakpoints :: [String] -> String
showBreakpoints bs =
  let enumeratedBreakpoints = zip ([1..] :: [Int]) (reverse bs)
  in intercalate "\n" ["(" ++ show d ++ ") " ++ b | (d, b) <- enumeratedBreakpoints]

-- | Print a line to the 'output' 'Handle'. The end-of-line character depends on whether we are
-- running in interactive mode (i.e. whether 'tty' is set). In interactive mode, the end of line is
-- a ' ', and the user is prompted for input at the end of the same line. In non-interactive mode,
-- each line of output is terminated by a '\n' character.
printLine :: String -> TerminalCoroutine ()
printLine s = do
  st <- lift get
  let endChar = if tty st then " " else "\n"
  liftIO $ hPutStr (output st) $ s ++ endChar

type TerminalParser = ParsecT String () Identity

class Tokens ps rs | ps -> rs where
  trimmedTokens :: ps -> TerminalParser rs

  tokens :: ps -> TerminalParser rs
  tokens ps = spaces *> trimmedTokens ps <* spaces

instance {-# OVERLAPPING #-} Tokens (TerminalParser a1, TerminalParser a2) (a1, a2) where
  trimmedTokens (p1, p2) = do
    r1 <- try $ p1 <* space
    spaces
    r2 <- try p2
    return (r1, r2)

instance {-# OVERLAPPABLE #-} ( TupleCons ps, TupleCons rs
                              , Tokens (Tail ps) (Tail rs)
                              , Head ps ~ TerminalParser a1
                              , Head rs ~ a1
                              ) => Tokens ps rs where
  trimmedTokens ps = do
    r1 <- try $ thead ps <* space
    spaces
    r2 <- trimmedTokens $ ttail ps
    return $ tcons r1 r2

str :: String -> TerminalParser String
str s = try (string s) <?> s

tok :: String -> TerminalParser String
tok t = spaces *> str t <* spaces

integer :: (Read a, Integral a) => TerminalParser a
integer = try (fmap read $ spaces *> raw <* spaces) <?> "integer"
  where raw = do sign <- optionMaybe $ oneOf "+-"
                 num <- many1 digit
                 case sign of
                   Just s -> return $ s : num
                   Nothing -> return num

predicate :: TerminalParser String
predicate = try (many1 $ satisfy $ not . isSpace) <?> "predicate"

step :: TerminalParser Command
step = (tok "step" <|> tok "s") >> return Step

next :: TerminalParser Command
next = (tok "next" <|> tok "n") >> return Next

finish :: TerminalParser Command
finish = (tok "finish" <|> tok "f") >> return Finish

continue :: TerminalParser Command
continue = (tok "continue" <|> tok "c") >> return Continue

setBreak :: TerminalParser Command
setBreak = do (_, p) <- tokens ( str "break" <|> str "b"
                               , predicate
                               )
              return $ SetBreakpoint p

deleteBreak :: TerminalParser Command
deleteBreak = do (_, b) <- tokens ( str "db" <|> str "delete-breakpoint"
                                  , liftM Right integer <|> liftM Left predicate
                                  )
                 return $ DeleteBreakpoint b

infoBreakpoints :: TerminalParser Command
infoBreakpoints = (tok "breakpoints" <|> tok "bs") >> return InfoBreakpoints

goals :: TerminalParser Command
goals = do (_, n) <- tokens ( str "goals" <|> str "gs"
                            , integer
                            )
           return $ InfoStack (Just n)
        <|> ((tok "goals" <|> tok "gs") >> return (InfoStack Nothing))
        <|> ((tok "goal" <|> tok "g") >> return (InfoStack $ Just 1))

help :: TerminalParser Command
help = (tok "help" <|> tok "h" <|> tok "?") >> return Help

commandParsers :: [TerminalParser Command]
commandParsers = [step, next, finish, continue, setBreak, deleteBreak, infoBreakpoints, goals, help]

-- | Read a 'Command' from a string. This accounts for short aliases of commands. For example,
--
-- >>> parseCommand "step"
-- Just Step
--
-- >>> parseCommand "s"
-- Just Step
parseCommand :: String -> TerminalCoroutine (Either ParseError Command)
parseCommand s = do
  st <- lift get

  let repeatLast = eof >> return (lastCommand st)
      command p = spaces *> p <* spaces <* eof
      parser = (foldl1' (<|>) (map command commandParsers) <?> "command") <|> repeatLast

  return $ parse parser "" s

-- | Read a 'Command' from the input file handle. If the input is not a valid command, an error
-- message is shown and the user is prompted to re-enter the command. This loop continues until a
-- valid command is entered.
getCommand :: TerminalCoroutine Command
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
runCommand :: DebugContext -> Command -> TerminalCoroutine Bool
runCommand context@DC { stack = s } c = do
  st <- lift get
  result <- case c of
    Step -> lift (put st { currentTarget = Any }) >> return True
    Next -> lift (put st { currentTarget = Depth $ length s }) >> return True
    Finish -> lift (put st { currentTarget = Depth $ length s - 1 }) >> return True
    Continue -> lift (put st { currentTarget = Breakpoint }) >> return True
    SetBreakpoint p
      | p `elem` breakpoints st ->
          printLine ("Breakpoint " ++ p ++ " already exists.") >> return False
      | otherwise -> do
          lift (put st { breakpoints = p : breakpoints st })
          printLine $ "Set breakpoint on " ++ p ++ "."
          return False
    DeleteBreakpoint (Left p)
      | p `elem` breakpoints st -> do
          lift (put st { breakpoints = delete p $ breakpoints st})
          printLine $ "Deleted breakpoint " ++ p ++ "."
          return False
      | otherwise -> printLine ("No breakpoint \"" ++ p ++ "\".") >> return False
    DeleteBreakpoint (Right i)
      | i > 0 && i <= length (breakpoints st) ->
          runCommand context (DeleteBreakpoint $ Left $ reverse (breakpoints st) !! (i - 1))
      | otherwise -> printLine "Index out of range." >> return False
    InfoBreakpoints -> printLine (showBreakpoints $ breakpoints st) >> return False
    InfoStack (Just n)
      | n > 0 -> printLine (showStack (Just n) s) >> return False
      | otherwise -> printLine "Argument must be positive." >> return False
    InfoStack Nothing -> printLine (showStack Nothing s) >> return False
    Help -> printLine debugHelp >> return False

  lift $ modify $ \st' -> st' { lastCommand = c }

  return result

-- | Read and evalute commands until a command is entered which causes control to be yielded back to
-- the solver.
repl :: DebugContext -> TerminalCoroutine ()
repl context = do
  c <- getCommand
  shouldYield <- runCommand context c
  unless shouldYield $ prompt context

-- | Entry point when yielding control from the solver to the terminal. This function outputs a
-- message to the user based on the yielded context, and then enters the interactive 'repl'.
prompt :: DebugContext -> TerminalCoroutine ()
prompt context@DC { stack = s, status = mtype, msg = m } = do
  st <- lift get
  let shouldStop = case currentTarget st of
                      Any -> True
                      Depth d -> length s <= d
                      Breakpoint
                        | mtype == Call ->
                          case head s of
                            PredGoal (Predicate p _) _ -> p `elem` breakpoints st
                            _ -> False
                        | otherwise -> False
  when shouldStop $ do
    liftIO $ hPutStr (output st) $ "(" ++ show (length s) ++ ") "
    liftIO $ setSGR [msgColor mtype | useColors st]
    liftIO $ hPutStr (output st) $ show mtype ++ ": "
    liftIO $ setSGR []
    printLine m
    repl context

-- | A coroutine which controls the HSPL solver, yielding control at every important event.
solverCoroutine :: Monad m => Goal -> SolverCoroutine m [ProofResult]
solverCoroutine g =
  observeAllSolverT (unDebugSolverT $ prove g >>= getResult)
                    Solver { goalStack = [] }

-- | A coroutine which controls the interactive debugger terminal, periodically yielding control to
-- the solver.
terminalCoroutine :: TerminalCoroutine ()
terminalCoroutine = await >>= \mc -> when (isJust mc) $ do
  prompt $ fromJust mc
  terminalCoroutine

-- | Run the debugger with the given configuration and goal. The result of this function is a
-- computaion in the 'IO' monad which, when executed, will run the debugger.
debug :: DebugConfig -> Goal -> IO [ProofResult]
debug c g =
  let cr = weave sequentialBinder weaveAwaitMaybeYield terminalCoroutine (solverCoroutine g)
      st = pogoStick runIdentity cr
  in fmap snd $ runDebugStateT c st -- Keep the solver output, ignore the terminal output
