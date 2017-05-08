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
-- >>> getAllSolutions $ syllogism ? "mortal" $$ (string "x")
-- [mortal("hypatia")]
syllogism :: Hspl
syllogism = hspl $ do
  def "mortal" (string "x") |- "human" $$ string "x"
  def "human" "hypatia"

-- | A contrived example ADT.
data Widget = Gibber Int
            | Wuzzle String
  deriving (Show, Eq, Typeable, Data)

-- | A somewhat contrived example showcasing the usage of ADT constructors in HSPL pattern matching.
--
-- >>> getAllSolutions $ adts ? "goodWidget" $$ (Wuzzle |$| string "x")
-- [goodWidget(Wuzzle "foo")]
--
-- >>> getAllSolutions $ adts ? "goodWidget" $$ (Gibber |$| int "x")
-- []
adts :: Hspl
adts = hspl $ do
  def "goodName" "foo"
  def "goodWidget" (Wuzzle |$| string "x") |- "goodName" $$ string "x"

-- | A simple example illustrating the use of lists in HSPL.
--
-- >>> getAllSolutions $ lists ? "member" $$ (int "x", [1, 2, 3] :: [Int])
-- [member(3, 1, 2, 3),member(2, 1, 2, 3),member(1, 1, 2, 3)]
lists :: Hspl
lists = hspl $ do
  def "member" (int "x", int "x" <:> int |*| "xs")
  def "member" (int "y", int "x" <:> int |*| "xs") |- "member" $$ (int "y", int |*| "xs")
