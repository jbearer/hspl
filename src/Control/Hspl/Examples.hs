{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Examples
Description : Example programs showcasing the features of HSPL.
Stability   : Experimental

This module contains example programs which are meant to illustrate the various capabilites of HSPL.
-}
module Control.Hspl.Examples where

import Data.Data

import Control.Hspl

-- | A classic example of modus ponens: all humans are mortal, and Hypatia is human. Therefore,
-- Hypatia is mortal.
--
-- >>> getAllSolutions $ runHspl syllogism $ "mortal"? (string "x")
-- [mortal("hypatia")]
syllogism :: Hspl
syllogism = hspl $ do
  def "mortal"? string "x" |- "human"? string "x"
  def "human"? "hypatia"

-- | A contrived example ADT.
data Widget = Gibber Int
            | Wuzzle String
  deriving (Show, Eq, Typeable, Data)

-- | A somewhat contrived example showcasing the usage of ADT constructors in HSPL pattern matching.
--
-- >>> getAllSolutions $ runHspl adts $ "goodWidget"? (Wuzzle $$ string "x")
-- [goodWidget(Wuzzle "foo")]
--
-- >>> getAllSolutions $ runHspl adts $ "goodWidget"? (Gibber $$ int "x")
-- []
adts :: Hspl
adts = hspl $
  def "goodWidget"? (Wuzzle $$ string "x") |- auto "x" |=| "foo"

-- | A simple example illustrating the use of lists in HSPL.
--
-- >>> getAllSolutions $ runHspl lists $ "member"? (int "x", [1, 2, 3] :: [Int])
-- [member(3, 1, 2, 3),member(2, 1, 2, 3),member(1, 1, 2, 3)]
--
-- >>> getAllSolutions $ runHspl lists $ "member"? (int "x", [1, 1] :: [Int])
-- [member(1, 1, 1),member(1, 1, 1)]
--
-- >>> getAllSolutions $ runHspl lists $ "distinct"? (int "x", [1, 1] :: [Int])
-- [member(1, 1, 1)]
lists :: Hspl
lists = hspl $ do
  def "member"? (int "x", int "x" <:> int |*| "xs")
  def "member"? (int "y", int "x" <:> int |*| "xs") |- "member"? (int "y", int |*| "xs")

-- | Example illustrating the difference between '(|=|)' and '(|==|)'.
--
-- >>> getAllSolutions $ runHspl equals $ "isFoo"? (string "x")
-- []
--
-- >>> getAllSolutions $ runHspl equals $ "isFoo"? "foo"
-- [isFoo("foo")]
--
-- >>> getAllSolutions $ runHspl equals $ "couldBeFoo"? (string "x")
-- [couldBeFoo("foo")]
equals :: Hspl
equals = hspl $ do
  def "isFoo"? string "x" |- auto "x" |==| "foo"
  def "couldBeFoo"? string "x" |- auto "x" |=| "foo"
