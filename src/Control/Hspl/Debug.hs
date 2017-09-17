{-|
Module      : Control.Hspl.Debug
Description : An interactive debugger for HSPL programs.
Stability   : Experimental

This module provides a way to run HSPL programs interactively. After each step of the computation,
the debugger will stop, print some information, and wait for input. The user can control the flow
of executions using various commands, which can be listed by typing "help" at the debugger prompt.
-}
module Control.Hspl.Debug (
    DebugConfig (..)
  , debugConfig
  , debugWith
  , debug
  ) where

import Control.Hspl
import qualified Control.Hspl.Internal.Debugger as D
import Control.Hspl.Internal.Debugger (DebugConfig (..), debugConfig)
import Control.Hspl.Internal.Syntax

-- | Prove the given goal in an interactive debugger with the given configuration options.
debugWith :: DebugConfig -> Goal -> IO [ProofResult]
debugWith c g = D.debug c $ astGoal g

-- | Run the debugger with the default configuration (see 'debugConfig').
debug :: Goal -> IO [ProofResult]
debug = debugWith debugConfig
