{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.List
Description : Predefined predicates for working with lists in HSPL.
Stability   : Experimental

This module provides efficient implementations of many common list operations, such as finding the
'length' of a list, checking whether an element is a 'member' of a list, and so on.

Because many of the functions defined here share names with standard library functions, this module
is designed to be imported qualified, as in

@
  import Control.Hspl
  import qualified Control.Hspl.List as L

  trivial :: Predicate ()
  trivial = predicate "trivial" $
    match () |- L.length ("foo", 3)
@
-}
module Control.Hspl.List (
    member
  , length
  , delete
  , nth
  ) where

import Prelude hiding (length)

import Control.Hspl
import Data.CallStack

listPred :: (TermEntry t, HasCallStack) => String -> PredicateBody t -> Predicate t
#if MIN_VERSION_base(4,8,1)
listPred = predicate
#else
listPred = predicate' [Scope "Control.Hspl.List"]
#endif

-- | @member? (x, xs)@ succeeds if @x@ is a member of @xs@. There are three primary modes of use:
--
-- 1. If both arguments are instantiated, 'member' can be used to determine if an element is in a
--    given list.
-- 2. If the first argument is a variable, but the second argument is instantiated, 'member' will
--    nondeterministically bind the variable to each member of the list.
-- 3. If the first argument is instantiated, but the second argument is a variable, 'member' will
--    generate lists, placing the given element at each position in the list. This usage will
--    succeed infinitely many times.
member :: forall a. TermEntry a => Predicate (a, [a])
member = listPred "member" $ do
  match (v"x", v"x" .:. __)
  match (v"x", v"y" .:. v"xs") |- member? (v"x" :: Var a, v"xs")

-- | @length? (xs, l)@ succeeds if @l@ is the length of @xs@. If @l@ is a variable, it is bound to
-- the length of the list.
length :: forall a. TermEntry a => Predicate ([a], Int)
length = listPred "length" $ do
  match ([] :: [a], 0 :: Int)
  match (__ .:. v"xs", v"l") |- do
    length? (v"xs" :: Var [a], v"l2")
    int "l" .==. int "l2" .+. (1 :: Int)

-- | Delete matching elements from a list. @delete? (xs, x, ys)@ succeeds when @ys@ is a list
-- containing all elements from @xs@ except those which unify with @x@.
delete :: forall a. TermEntry a => Predicate ([a], a, [a])
delete = listPred "delete" $
  match (v"in", v"elem", v"out") |-
    findAll (v"x" :: Var a) (select? (v"in", v"elem", v"x")) (v"out")
  where select :: Predicate ([a], a, a)
        select = listPred "delete.select" $
                    match (v"xs", v"ignore", v"x") |- do
                      member? (v"x" :: Var a, v"xs")
                      v"x" ./=. (v"ignore" :: Var a)

-- | @nth? (n, xs, x)@ succeeds if @x@ is the @n@th element of @xs@ (counting starts at 0). There
-- are four primary modes of use:
--
-- 1. If @xs@ and @x@ are instantiated, but @n@ is a variable, 'nth' will bind @n@ to the index of
--    @x@.
-- 2. If @n@ and @xs@ are instantiated, but @x@ is a variable, 'nth' will bind @x@ to the @n@th
--    element of @xs@.
-- 3. If neither @n@ nor @x@ are instantiated, 'nth' will enumerate the list @xs@.
-- 4. If neither @n@ nor @xs@ are instantiated, 'nth' will generate successively longer list
-- prefixes ending in @x@, and bind @n@ to the correct index.
--
-- 'nth' currently uses an efficient implementation ported from the SWI Prolog standard library.
nth :: forall a. TermEntry a => Predicate (Int, [a], a)
nth = listPred "nth" $
  match (v"index", v"list", v"elem") |-
    cond $ do
      unified? int "index" ->> nthDet? (int "index", v"list", v"elem")
      true ->> do (v"head" :: Var a) .:. v"tail" .=. v"list"
                  nthGen? (v"tail", v"elem", v"head", 0::Int, v"index")

  where
    -- Take the nth element deterministically, with 6-way loop unrolling
    nthDet :: Predicate (Int, [a], a)
    nthDet = listPred "nth.det" $ do
      match (0::Int, v"e" .:. __, v"e") |- cut
      match (1::Int, [__, v"e"] .++. __, v"e") |- cut
      match (2::Int, [__, __, v"e"] .++. __, v"e") |- cut
      match (3::Int, [__, __, __, v"e"] .++. __, v"e") |- cut
      match (4::Int, [__, __, __, __, v"e"] .++. __, v"e") |- cut
      match (5::Int, [__, __, __, __, __, v"e"] .++. __, v"e") |- cut
      match (v"n", [__, __, __, __, __, __, v"head"] .++. v"tail", v"elem") |- do
        v"m" .==. v"n" .-. (6::Int)
        v"m" .>=. (0::Int)
        nthDet? (v"m", v"head" .:. v"tail", v"elem")

    -- generate lists with elem at the ith position
    nthGen :: Predicate ([a], a, a, Int, Int)
    nthGen = listPred "nth.gen" $ do
      match (__, v"elem", v"elem", v"base", v"base")
      match (v"head" .:. v"tail", v"elem", __, int "n", v"base") |- do
        successor? (int "n", int "m")
        nthGen? (v"tail", v"elem", v"head", v"m", v"base")
