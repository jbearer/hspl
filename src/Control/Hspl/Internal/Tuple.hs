{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Interal.Tuple
Description : Utilities for generic operations on tuples and curried functions.
Stability   : Internal

This module defines a collection of utilities for manipulating tuples. These utilities were built
out independently in different parts of the project before being collected here, fleshed out, and
given a single interface. As such, the module is currently very ad hoc. For example, there is no
relationship between 'TupleCons' and associated functions, and the rest of the module. Hopefully one
day this will be refactored into a more unified, complete abstraction.
-}
module Control.Hspl.Internal.Tuple (
  -- * Representation
  -- | A common problem when trying to write generic tuple operations is the edge case that arises
  -- from singleton tuples -- which, as far as Haskell is concerned, are not tuples at all. To
  -- mitigate this problem, we define a 'Tuple' wrapper which is parameterized by the type of the
  -- tuple contained as well as a phantom type indicating if the contained value is a singleton
  -- tuple ('One') or not ('Many').
    Tuple (..)
  , Tupleable (..)
  -- * Inspecting tuples and functions
  -- ** Tuple size
  , Card (..)
  , One
  , Many
  -- ** Functions
  , Arity
  , Arg
  , Result
  -- * List-like operations on tuples
  , TupleCons (..)
  , thead
  , ttail
  ) where

-- | Tuple "cardinality". Used to indicate whether a 'Tuple' is a 'Singleton' or a true tuple. This
-- data structure is intended to be promoted to a type with @DataKinds@ and used as a phantom type
-- for tagging 'Tuple's. To avoid having ticks everywhere, use the helper types 'One' and 'Many'
-- rather than using the constructors 'DOne' and 'DMany' directly.
data Card = DOne | DMany

-- | The cardinality of a 'Singleton' 'Tuple'.
type One = 'DOne

-- | The cardinality of a true 'Tuple'.
type Many = 'DMany

-- | Abstract representation of a tuple. @Tuple a Many@ represents a true tuple, while @Tuple a One@
-- represents a singleton tuple. For example, @Singleton 'a'@ is the representation of a conceptual
-- singleton tuple @('a',)@. @Tuple ('a', 'b')@ represents the plain tuple @('a', 'b')@, while
-- @Singleton ('a', 'b')@ can be used to represent a nested singleton tuple @(('a', 'b'),)@.
data Tuple a (n :: Card) where
  Singleton :: a -> Tuple a One
  Tuple :: a -> Tuple a Many

instance Show a => Show (Tuple a n) where
  show (Singleton a) = "Singleton (" ++ show a ++ ")"
  show (Tuple a) = "Tuple (" ++ show a ++ ")"

instance Eq a => Eq (Tuple a n) where
  (==) (Singleton a) (Singleton a') = a == a'
  (==) (Tuple a) (Tuple a') = a == a'

-- | The cardinality of the arguments to a function. In other words, @Arity f@ is the cardinality
-- of the type of tuple that would be passed to an uncurried version of @f@.
type family Arity f where
  Arity (a -> b -> c) = Many -- Catches all functions of 2 or more arguments
  Arity (a -> b) = One

-- | The result type of a curried function after it has been applied to as many arguments as it can
-- be applied to. For example,
--
-- prop> Result map ~ [b]
type family Result f where
  Result (a -> b) = Result b
  Result a = a

-- | The argument type of an uncurried version of a function. For example,
--
-- prop> Arg map ~ (a -> b, [a])
type family Arg f where
  Arg (a -> b -> c -> d -> e -> f -> g -> h) = (a, b, c, d, e, f, g)
  Arg (a -> b -> c -> d -> e -> f -> g) = (a, b, c, d, e, f)
  Arg (a -> b -> c -> d -> e -> f) = (a, b, c, d, e)
  Arg (a -> b -> c -> d -> e) = (a, b, c, d)
  Arg (a -> b -> c -> d) = (a, b, c)
  Arg (a -> b -> c) = (a, b)
  Arg (a -> b) = a

-- | A class facilitating the "wrapping" of plain tuples (or singleton values) in a 'Tuple' object.
class Tupleable a (b :: Card) where
  -- | Get the abstract representation of a tuple. The cardinality parameter of the result type is
  -- intentionally ambiguous -- depending on the context, @mkTuple ('a', 'b')@ may represent a true
  -- tuple of size two, or it may represent a singleton tuple whose only element is a tuple of size
  -- two.
  mkTuple :: a -> Tuple a b

instance Tupleable a One where
  mkTuple = Singleton
instance Tupleable (a, b) Many where
  mkTuple = Tuple
instance Tupleable (a, b, c) Many where
  mkTuple = Tuple
instance Tupleable (a, b, c, d) Many where
  mkTuple = Tuple
instance Tupleable (a, b, c, d, e) Many where
  mkTuple = Tuple
instance Tupleable (a, b, c, d, e, f) Many where
  mkTuple = Tuple
instance Tupleable (a, b, c, d, e, f, g) Many where
  mkTuple = Tuple

-- | A class supporting overloaded list-like operations on tuples.
class TupleCons a where
  -- | The type of the first element of the tuple.
  type Head a

  -- | The type of the tuple containing all elements but the first.
  type Tail a

  -- | Prepend an element to a tuple.
  tcons :: Head a -> Tail a -> a

  -- | Split a tuple into a head and a tail.
  tuncons :: a -> (Head a, Tail a)

-- | Get the first element of a tuple.
thead :: TupleCons a => a -> Head a
thead t = let (x, _) = tuncons t in x

-- | Get the tuple containg all elements but the first.
ttail :: TupleCons a => a -> Tail a
ttail t = let (_, xs) = tuncons t in xs

instance TupleCons (a, b) where
  type Head (a, b) = a
  type Tail (a, b) = b
  tcons a b = (a, b)
  tuncons (a, b) = (a, b)

#define TUPLE_CONS(xs) \
instance TupleCons (x, xs) where \
  type Head (x, xs) = x; \
  type Tail (x, xs) = (xs); \
  tcons x (xs) = (x, xs); \
  tuncons (x, xs) = (x, (xs)); \

#define X ,

TUPLE_CONS(a X b)
TUPLE_CONS(a X b X c)
TUPLE_CONS(a X b X c X d)
TUPLE_CONS(a X b X c X d X e)
TUPLE_CONS(a X b X c X d X e X f)
TUPLE_CONS(a X b X c X d X e X f X g)

#undef TUPLE_CONS
#undef X
