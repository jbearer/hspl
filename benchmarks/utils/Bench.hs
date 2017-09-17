{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}

module Bench (
    Benchmark
  , takeDirectory
  , (</>)
  , compareTo
  , bench
  , assert
  , assertEquals
  ) where

import Control.Hspl.Internal.Ast ( Term (..)
                                 , ListTerm (..)
                                 , TupleTerm (..)
                                 , Var (..)
                                 , Goal (..)
                                 , Predicate (..)
                                 , termMap
                                 , fromTerm
                                 )
import qualified Control.Hspl.Internal.Ast as Ast
import Control.Hspl.Internal.Syntax

import Control.Hspl
import qualified Control.Hspl as Hspl

import Control.Exception (evaluate)
import Control.Monad.State
import Data.Char
import Data.Data
import Data.List
import Data.Time.Clock
import Data.CallStack
import GHC.Generics
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process
import Text.PrettyPrint.Tabulate

data BenchFlag = SkipProlog
               | IncludeKey String
               | ExcludeKey String
               | Help
  deriving (Eq)

data BenchConfig = Config { shouldUseProlog :: Bool
                          , includeKeys :: [String]
                          , excludeKeys :: [String]
                          }

data BenchResult = BenchResult { benchResultKey :: String
                               , benchResultHspl :: NominalDiffTime
                               , benchResultProlog :: NominalDiffTime
                               , benchResultFactor :: Double
                               }
  deriving (Typeable, Data, Generic)
instance Tabulate BenchResult
instance CellValueFormatter NominalDiffTime

data BenchState = BenchState { config :: BenchConfig
                             , benchmarks :: [BenchResult]
                             , prologExecutable :: String
                             , prologFile :: FilePath
                             }

type Benchmark = StateT BenchState IO

type StackFrame = (String, SrcLoc)

printBenchResults :: [BenchResult] -> IO ()
printBenchResults = printTable

parseArgs :: IO BenchConfig
parseArgs = do
  args <- getArgs
  let options =
        [ Option "" ["include"] (ReqArg IncludeKey "KEY") "run benchmark KEY, rather than all benchmarks (additive)"
        , Option "" ["exclude"] (ReqArg ExcludeKey "KEY") "do not run benchmark KEY (additive)"
        , Option "" ["no-prolog"] (NoArg SkipProlog) "do not run prolog comparison"
        , Option "h" ["help"] (NoArg Help) "show this help and exit"
        ]
  let (flags, extras, errors) = getOpt RequireOrder options args
  unless (null errors) $ fail $ unlines errors
  unless (null extras) $ fail $ "Unrecognized arguments: " ++ intercalate ", " extras

  when (Help `elem` flags) $ do
    putStrLn $ usageInfo "hspl-bench" options
    exitSuccess

  return Config { shouldUseProlog = SkipProlog `notElem` flags
                , includeKeys = [key | IncludeKey key <- flags]
                , excludeKeys = [key | ExcludeKey key <- flags]
                }

compareTo :: FilePath -> Benchmark a -> IO a
compareTo p b = do
  c <- parseArgs
  prolog <- if shouldUseProlog c then findPrologExecutable else return "false"

  let initialState = BenchState { benchmarks = []
                                , prologExecutable = prolog
                                , prologFile = p
                                , config = c
                                }

  (result, st) <- runStateT b initialState

  putStrLn "Results:"
  let hsplTotal = sum $ map benchResultHspl $ benchmarks st
  let plTotal = sum $ map benchResultProlog $ benchmarks st
  let factor = if plTotal == 0 then 0 else toRational hsplTotal / toRational plTotal
  let summary = BenchResult { benchResultKey = "Total"
                            , benchResultHspl = hsplTotal
                            , benchResultProlog = plTotal
                            , benchResultFactor = fromRational factor
                            }
  printBenchResults $ benchmarks st ++ [summary]

  return result

findPrologExecutable :: IO String
findPrologExecutable = go ["swipl", "prolog"]
  where go [] = fail "Unable to find a valid Prolog executable. Is Prolog installed?"
        go (candidate:rest) = do
          handle <- spawnProcess candidate ["-t", "halt"]
          exitCode <- waitForProcess handle
          case exitCode of
            ExitSuccess -> return candidate
            ExitFailure i
              | i == 127 -> go rest
              | otherwise -> fail $ "Unexpected exit code " ++ show i ++ " when trying candidate " ++
                                    "Prolog executable '" ++ candidate ++ "'"

callProlog :: String -> FilePath -> IO ()
callProlog exe srcFile = callProcess exe ["-l", srcFile, "-t", "hsplRun"]

compileProlog :: FilePath -> Ast.Goal -> IO FilePath
compileProlog srcFile g = do
  tmp <- getTemporaryDirectory
  UTCTime { utctDayTime=ts } <- getCurrentTime
  let outFile = tmp </> "hspl-bench-" ++ show ts ++ ".pl"

  copyFile srcFile outFile
  appendFile outFile $ unlines
    [ ""
    , "%%% BEGIN GENERATED GOAL %%%"
    , "hsplRun :- " ++ genPrologGoal g ++ "."
    ]

  return outFile

shouldExecute :: String -> [String] -> [String] -> Bool
shouldExecute key include exclude
  | key `elem` include = True
  | not $ null include = False
  | key `elem` exclude = False
  | otherwise = True

bench :: String -> Hspl.Goal -> Benchmark (Maybe [ProofResult])
bench key gw = do
  st@BenchState {..} <- get
  if shouldExecute key (includeKeys config) (excludeKeys config)
    then do
      hsplStart <- liftIO getCurrentTime
      results <- liftIO $ evaluate $ runHspl gw
      hsplEnd <- liftIO getCurrentTime
      let hsplResult = diffUTCTime hsplEnd hsplStart

      (plResult, factor) <-
        if shouldUseProlog config
          then do
            compiledProlog <- liftIO $ compileProlog prologFile $ astGoal gw
            plStart <- liftIO getCurrentTime
            liftIO $ callProlog prologExecutable compiledProlog
            plEnd <- liftIO getCurrentTime
            let plResult = diffUTCTime plEnd plStart
            let factor = toRational hsplResult / toRational plResult
            return (plResult, factor)
          else
            return (0, 0)

      assert "no duplicate keys" $ not $ any ((==key) . benchResultKey) benchmarks
      let benchResult = BenchResult { benchResultKey = key
                                    , benchResultHspl = hsplResult
                                    , benchResultProlog = plResult
                                    , benchResultFactor = fromRational factor
                                    }
      put $ st { benchmarks = benchmarks ++ [benchResult] }

      return $ Just results
    else
      return Nothing

showFrame :: StackFrame -> String
showFrame (_, loc) = concat [ srcLocFile loc, ":"
                            , show $ srcLocStartLine loc, ":"
                            , show $ srcLocStartCol loc, " in "
                            , srcLocPackage loc, ":", srcLocModule loc
                            ]

location :: HasCallStack => String
location = case reverse callStack of
  (f:_) -> showFrame f
  [] -> "<no location>"

assert :: (HasCallStack, Monad m) => String -> Bool -> m ()
assert _ True = return ()
assert msg False = error $ "Assertion error (assert " ++ msg ++ ") at " ++ location

assertEquals :: (HasCallStack, Show a, Eq a, Monad m) => a -> a -> m ()
assertEquals expected actual = assert (show expected ++ " == " ++ show actual) (expected == actual)

genPrologTerm :: TermEntry a => Term a -> String
genPrologTerm (Constant c) = prologAtomCase $ show c

genPrologTerm (Variable (Var x)) = prologVarCase x
genPrologTerm (Variable (Fresh n)) = prologVarCase $ "Fresh" ++ show n
genPrologTerm (Variable Anon) = "_"

genPrologTerm (Constructor c []) = prologAtomCase $ show c
genPrologTerm (Constructor c ts) =
  prologAtomCase (show c) ++ "(" ++ intercalate "," (map (termMap genPrologTerm) ts) ++ ")"

genPrologTerm (Tup tup) = "[" ++ joinTup tup ++ "]"

genPrologTerm term@(List list) =
  case fromTerm term >>= cast of
    Just str -> prologAtomCase str
    Nothing -> "[" ++ joinList list ++ "]"
  where joinList Nil = ""
        joinList (Cons t Nil) = genPrologTerm t
        joinList (Cons t ts) = genPrologTerm t ++ "," ++ joinList ts
        joinList (VarCons t (Var xs)) = genPrologTerm t ++ "|" ++ prologAtomCase xs
        joinList (VarCons t (Fresh n)) = genPrologTerm t ++ "|" ++ prologAtomCase ("Fresh" ++ show n)

genPrologTerm (Sum t1 t2) = "(" ++ genPrologTerm t1 ++ ") + (" ++ genPrologTerm t2 ++ ")"
genPrologTerm (Difference t1 t2) = "(" ++ genPrologTerm t1 ++ ") - (" ++ genPrologTerm t2 ++ ")"
genPrologTerm (Product t1 t2) = "(" ++ genPrologTerm t1 ++ ") * (" ++ genPrologTerm t2 ++ ")"
genPrologTerm (Quotient t1 t2) = "(" ++ genPrologTerm t1 ++ ") / (" ++ genPrologTerm t2 ++ ")"
genPrologTerm (IntQuotient t1 t2) = "div(" ++ genPrologTerm t1 ++ "," ++ genPrologTerm t2 ++ ")"
genPrologTerm (Modulus t1 t2) = "mod(" ++ genPrologTerm t1 ++ "," ++ genPrologTerm t2 ++ ")"

genPrologGoal :: Ast.Goal -> String
genPrologGoal (PredGoal (Predicate name arg) _) = prologAtomCase name ++ "(" ++ expand arg ++ ")"
  where expand (Tup tup) = joinTup tup
        expand t = genPrologTerm t

genPrologGoal (CanUnify t1 t2) = "(" ++ genPrologTerm t1 ++ ") = (" ++ genPrologTerm t2 ++ ")"
genPrologGoal (Identical t1 t2) = "(" ++ genPrologTerm t1 ++ ") == (" ++ genPrologTerm t2 ++ ")"
genPrologGoal (Equal t1 t2) = "(" ++ genPrologTerm t1 ++ ") is (" ++ genPrologTerm t2 ++ ")"
genPrologGoal (LessThan t1 t2) = "(" ++ genPrologTerm t1 ++ ") < (" ++ genPrologTerm t2 ++ ")"

genPrologGoal (IsUnified t) = error "No Prolog analog for IsUnified"
genPrologGoal (IsVariable t) = "var(" ++ genPrologTerm t ++ ")"

genPrologGoal (Not g) = "\\+(" ++ genPrologGoal g ++ ")"
genPrologGoal (And g1 g2) = "(" ++ genPrologGoal g1 ++ "," ++ genPrologGoal g2 ++ ")"
genPrologGoal (Or g1 g2) = "(" ++ genPrologGoal g1 ++ ";" ++ genPrologGoal g2 ++ ")"
genPrologGoal Top = "true"
genPrologGoal Bottom = "false"

genPrologGoal (Alternatives x g xs) =
  "findall(" ++ genPrologTerm x ++ "," ++ genPrologGoal g ++ "," ++ genPrologTerm xs ++ ")"

genPrologGoal (Once g) = "once(" ++ genPrologGoal g ++ ")"
genPrologGoal Cut = "!"

genPrologGoal (Track g) = genPrologGoal g

prologAtomCase :: String -> String
prologAtomCase "" = ""
prologAtomCase (c:cs) = toLower c : cs

prologVarCase :: String -> String
prologVarCase "" = ""
prologVarCase (c:cs) = toUpper c : cs

joinTup :: TermEntry a => TupleTerm a -> String
joinTup (Tuple2 t1 t2) = genPrologTerm t1 ++ "," ++ genPrologTerm t2
joinTup (TupleN t ts) = genPrologTerm t ++ "," ++ joinTup ts
