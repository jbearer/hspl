{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Examples
Description : Example programs showcasing the features of HSPL.
Stability   : Experimental

This module contains example programs which are meant to illustrate the various capabilites of HSPL.
-}
module Control.Hspl.Examples (
  -- * Syllogism
  -- $syllogism
    mortal
  , human
  -- * Using ADTs
  -- $adts
  , Widget (..)
  , goodWidget
  -- * Using lists
  -- $lists
  , member
  , distinct
  -- * Unification and equality
  -- $equals
  , isFoo
  , couldBeFoo
  -- * Infinite computations
  -- $odds
  , odds
  ) where

import Data.Data

import Control.Hspl
import Control.Hspl.Internal.Ast (TermEntry)

-- $syllogism
-- A classic example of modus ponens: all humans are mortal, and Hypatia is human. Therefore,
-- Hypatia is mortal.
--
-- >>> getAllSolutions $ runHspl $ mortal? string "x"
-- [mortal("hypatia")]

-- | Succeeds when the argument is mortal, which is true whenever the argument is human.
mortal :: Predicate String
mortal = predicate "mortal" $
  match(v"x") |- human? v"x"

-- | Defines the fact that Hypatia is human.
human :: Predicate String
human = predicate "human" $
  match "hypatia"

-- $adts
-- A somewhat contrived example showcasing the usage of ADT constructors in HSPL pattern matching.
--
-- >>> getAllSolutions $ runHspl $ goodWidget? (Wuzzle $$ string "x")
-- [goodWidget(Wuzzle "foo")]
--
-- >>> getAllSolutions $ runHspl $ goodWidget? (Gibber $$ int "x")
-- []

-- | A contrived example ADT.
data Widget = Gibber Int
            | Wuzzle String
  deriving (Show, Eq, Typeable, Data)

-- | Succeeds only for the 'Widget' @Wuzzle "foo"@.
goodWidget :: Predicate Widget
goodWidget = predicate "goodWidget" $
  match (Wuzzle $$ string "x") |- v"x" |=| "foo"

-- $lists
-- A simple example illustrating the use of lists in HSPL.
--
-- >>> getAllSolutions $ runHspl $ member? (char "x", "abc")
-- [member('a', 'a', 'b', 'c'),member('b', 'a', 'b', 'c'),member('c', 'a', 'b', 'c')]
--
-- >>> getAllSolutions $ runHspl $ member? (int "x", [1, 1] :: [Int])
-- [member(1, 1, 1),member(1, 1, 1)]
--
-- >>> getAllSolutions $ runHspl $ distinct? (int "x", [1, 1] :: [Int])
-- [member(1, 1, 1)]

-- | @member? (v"x", [...])@ succeeds once for each element of the list, and binds that element to
-- the variable @"x"@. @member? (x, xs)@ succeeds if and only if @x@ is an element of @xs@.
member :: forall a. TermEntry a => Predicate (a, [a])
member = predicate "member" $ do
  let a :: String -> Var a
      a = v
  match (a"x", a"x" <:> v"xs")
  match (a"y", a"x" <:> v"xs") |- member? (a"y", a \* "xs")

-- | Similar to 'member', but if the first variable is unbound, 'distinct' succeeds only once for
-- each distinct element of the list.
distinct :: forall a. TermEntry a => Predicate (a, [a])
distinct = predicate "distinct" $ do
  match (v"x", v"x" <:> v"xs")
  match (v"y", v"x" <:> v"xs") |- do
    (v"y" :: Var a) |\=| (v"x" :: Var a)
    distinct? (v"y" :: Var a, v"xs" :: Var [a])

-- $equals
-- Example illustrating the difference between '|=|' and '|==|'.
--
-- >>> getAllSolutions $ runHspl $ isFoo? string "x"
-- []
--
-- >>> getAllSolutions $ runHspl $ isFoo? "foo"
-- [isFoo("foo")]
--
-- >>> getAllSolutions $ runHspl $ couldBeFoo? string "x"
-- [couldBeFoo("foo")]

-- | Succeeds if and only if the argument is identical to the string @"foo"@. No bindings are
-- created.
isFoo :: Predicate String
isFoo = predicate "isFoo" $
  match (v"x") |- v"x" |==| "foo"

-- | Succeeds if the argument can be unified with the string @"foo"@, and does so.
couldBeFoo :: Predicate String
couldBeFoo = predicate "couldBeFoo" $
  match (v"x") |- v"x" |=| "foo"

-- $odds
-- Example of a program with infinitely many solutions.
--
-- >>> getAllSolutions $ runHsplN 5 $ odds? int "x"
-- [odds(1),odds(3),odds(5),odds(7),odds(9)]

-- | @odds? v"x"@ succeeds once for every odd number, in ascending order and starting from @1@.
odds :: Predicate Int
odds = predicate "odds" $ do
  match(1 :: Int)
  match(v"x") |- do
    odds? v"y"
    v"x" `is` v"y" |+| (2 :: Int)
