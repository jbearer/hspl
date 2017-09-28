{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}
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
  -- * Goals
    GoalWriter (..)
  , Goal
  , Theorem
  , astGoal
  -- * Clauses
  , ClauseWriter (..)
  , PredicateBody
  , execClauseWriter
  , astClause
  -- * Conditionals
  , CondBranch (..)
  , CondWriter (..)
  , CondBody
  , execCond
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
-- The list built by this monad consists of functions which, when given a predicate constructor,
-- apply that constructor to an argument and use the resulting predicate to create a 'HornClause'.
newtype ClauseWriter t a =
  CW { unCW :: Writer [(Ast.ErasedTerm -> Ast.Predicate) -> Ast.HornClause] a }
  deriving (Functor, Applicative, Monad, MonadWriter [(Ast.ErasedTerm -> Ast.Predicate) -> Ast.HornClause])

-- | A definition of a predicate of type @t@.
type PredicateBody t = ClauseWriter t ()

-- | Extract the clause constructors from 'ClauseWriter'.
execClauseWriter :: ClauseWriter t a -> [(Ast.ErasedTerm -> Ast.Predicate) -> Ast.HornClause]
execClauseWriter = execWriter . unCW

-- | Retrieve the internal representation of a 'Ast.HornClause' from a 'Clause'.
astClause :: (forall e. Ast.TermEntry e => Ast.Term e -> Ast.Predicate) ->
             ClauseWriter t a -> [Ast.HornClause]
astClause f = map ($Ast.termMap f) . execClauseWriter

-- | A single branch of a conditional block, consisting of a condition 'Goal' and an action 'Goal'.
data CondBranch = Branch Goal Goal
  deriving (Show, Eq)

-- | The body of a conditional block. The 'MonadWriter' instance can be used for appending
-- 'CondBranch'es to the block.
newtype CondWriter a = CondWriter { unCondWriter :: Writer [CondBranch] a }
  deriving (Functor, Applicative, Monad, MonadWriter [CondBranch])

-- | The body of a conditional block.
type CondBody = CondWriter ()

-- | Retrieve the list of branches from a conditional block.
execCond :: CondWriter a -> [CondBranch]
execCond = execWriter . unCondWriter
