{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.Syntax
Description : A user-facing model and conversion functions to convert to and from the
              "Control.Hspl.Internal.Ast" model.
Stability   : Internal

This module defines the fundamental types which make up the logic programming model that is
presented to the user. Some of the types have instances which aid in the construction of HSPL
programs (e.g. the 'MonadWriter' instances for 'Goal' and 'Clause'), hence the necessity of the
module.

Also provided are functions to convert these user-facing types to their internal equivalents.
Functions for converting the other way are primarily provided through instances, e.g. 'tell'.
-}
module Control.Hspl.Internal.Syntax (
    GoalWriter (..)
  , Goal
  , Theorem
  , astGoal
  , ClauseWriter (..)
  , Clause
  , astClause
  ) where

import qualified Control.Hspl.Internal.Ast as Ast
import Control.Hspl.Internal.UI

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad.Writer

-- | A monad for appending 'Ast.Goal's to a conjunction.
newtype GoalWriter a = GW { unGW :: Writer Ast.Goal a }
  deriving (Functor, Applicative, Monad, MonadWriter Ast.Goal)

instance Eq (GoalWriter ()) where
  (==) g1 g2 = astGoal g1 == astGoal g2

instance Show (GoalWriter ()) where
  show = formatGoal . astGoal

-- | A statement to be proven.
type Goal = GoalWriter ()

-- | A statement which has been proven. A 'Theorem' is just a 'Goal' which has been proven.
type Theorem = Goal

-- | Extract the internal representation of a 'Ast.Goal' from a 'Goal'.
astGoal :: GoalWriter a -> Ast.Goal
astGoal = execWriter . unGW

-- | A monad for collecting the list of 'Ast.HornClause's which will define a 'Ast.Predicate'.
-- This monad creates a list of functions waiting for a predicate name. When applied to a string,
-- they produce clauses whose positive literals have that name.
newtype ClauseWriter t a = CW { unCW :: Writer [String -> Ast.HornClause] a }
  deriving (Functor, Applicative, Monad, MonadWriter [String -> Ast.HornClause])

-- | A definition of a predicate.
type Clause t = ClauseWriter t ()

-- | Retrieve the internal representation of a 'Ast.HornClause' from a 'Clause'.
astClause :: ClauseWriter t a -> [String -> Ast.HornClause]
astClause = execWriter . unCW
