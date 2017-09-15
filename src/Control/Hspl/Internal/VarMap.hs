{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.VarMap
Description : Efficient associative container for HSPL AST elements.
Stability   : Internal

This module defines a container which can map variables of different types to parameterized AST
elements (e.g. 'Var' or 'Term') of the same type. For example, the mapping

@
  Var "x" :: Var Char => toTerm 'a'
  Var "y" :: Var Bool => toTerm True
@

could be stored in a container of type @VarMap Term@.

This module is meant to be imported qualified to avoid naming conflicts, a la "Data.Map".
-}
module Control.Hspl.Internal.VarMap (
    VarMap (..)
  , Entry (..)
  , empty
  , singleton
  , insert
  , union
  , lookup
  , findWithDefault
  , containsKey
  , containsMapping
  , toList
  , fromList
  , collect
  , map
  , for
  , for_
  , SubMap (..)
  ) where

import Prelude hiding (lookup, map)
import qualified Prelude

import Control.Hspl.Internal.Ast

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid (Monoid (..))
import Data.Typeable

-- | A type-erased container mapping variables of one type to elements of the same type. This is
-- exported only for testability and should not be considered part of the interface of this module.
data SubMap f = forall a. (Show (f a), Eq (f a), TermEntry a) => SubMap (Map (Var a) (f a))
  deriving (Typeable)

instance Typeable f => Eq (SubMap f) where
  (==) (SubMap m) (SubMap m') = maybe False (==m) $ cast m'

-- | An associative container mapping variables to AST elements. The parameter @f@ is a type
-- constructor for the values. Any individual mapping will have a key of type @Var a@ and a value of
-- type @f a@. Note that @a@ may differ between mappings.
newtype VarMap f = VarMap { unVarMap :: Map TypeRep (SubMap f) }
  deriving (Eq)

-- | A type-erased wrapper for a single entry in a 'VarMap'. Useful for representing mappings in
-- homogeneous lists, such as in 'fromList' and 'toList'.
data Entry f = forall a. (Show (f a), Eq (f a), TermEntry a) => Entry (Var a) (f a)
deriving instance Show (Entry f)

instance Typeable f => Eq (Entry f) where
  (==) (Entry k v) (Entry k' v') = maybe False (== (k, v)) $ cast (k', v')

instance Typeable f => Show (VarMap f) where
  show m = "{" ++ intercalate ", " (collect (\k v -> show k ++ " => " ++ show v) m) ++ "}"

instance Typeable f => Monoid (VarMap f) where
  mempty = empty
  mappend = union

-- | A 'VarMap' with no elements.
empty :: VarMap f
empty = VarMap M.empty

-- | A 'VarMap' containing exactly one mapping.
singleton :: (TermEntry a, Typeable f, Show (f a), Eq (f a)) => Var a -> f a -> VarMap f
singleton k v = insert k v empty

-- | Retrieve the value associated with a given key.
lookup :: (TermEntry a, Typeable f) => Var a -> VarMap f -> Maybe (f a)
lookup key (VarMap typeMap) = do
  SubMap subMap <- M.lookup (varType key) typeMap
  subMap' <- cast subMap
  M.lookup key subMap'

-- | The left-biased union of two 'VarMap's. This is the operation used for 'mappend' in the
-- 'Monoid' instance.
union :: Typeable f => VarMap f -> VarMap f -> VarMap f
union (VarMap m1) (VarMap m2) = VarMap $ M.mapWithKey updateSubMap m1 `M.union` m2
  where updateSubMap :: Typeable f => TypeRep -> SubMap f -> SubMap f
        updateSubMap ty (SubMap m) =
          case M.lookup ty m2 of
            Just (SubMap m') -> case cast m' of
              Just m'' -> SubMap $ m `M.union` m''
              Nothing -> SubMap m
            Nothing -> SubMap m

-- | Retrieve the value associated with a given key, or a default value if that key is not in the
-- 'VarMap'.
findWithDefault :: (TermEntry a, Typeable f) => f a -> Var a -> VarMap f -> f a
findWithDefault d k m = fromMaybe d $ lookup k m

-- | Determine whether a key exists in the 'VarMap'. @containsKey k m@ is equivalent to
-- @isJust (lookup k m)@.
containsKey :: (TermEntry a, Typeable f) => Var a -> VarMap f -> Bool
containsKey k m = isJust $ lookup k m

-- | Determine whether a mapping exists in the 'VarMap'. If the key exists in the map,
-- 'containsMapping' will lookup the value associated with the key and compare it to the given
-- value. If the key does not exist in the map, the result will be 'False'.
containsMapping :: (TermEntry a, Typeable f, Eq (f a)) => Var a -> f a -> VarMap f -> Bool
containsMapping k v m = case lookup k m of
  Just v' -> v == v'
  Nothing -> False

-- | Insert a new mapping into the table, or update the value associated with an existing key.
insert :: forall a f. (TermEntry a, Typeable f, Show (f a), Eq (f a)) =>
                      Var a -> f a -> VarMap f -> VarMap f
insert key value (VarMap typeMap) =
  let subMap = fromMaybe (M.empty :: Map (Var a) (f a)) $
                extractSubMap $ M.lookup (varType key) typeMap
      subMap' = M.insert key value subMap
  in VarMap $ M.insert (varType key) (SubMap subMap') typeMap
  where extractSubMap :: Maybe (SubMap f) -> Maybe (Map (Var a) (f a))
        extractSubMap (Just (SubMap m)) = cast m
        extractSubMap Nothing = Nothing

-- | Apply a polymorphic function to each mapping in the table and produce a list of the results.
collect :: forall f r. Typeable f =>
          (forall a. (TermEntry a, Show (f a), Eq (f a)) => Var a -> f a -> r) -> VarMap f -> [r]
collect f = concatMap mapSubMap . M.toList . unVarMap
  where mapSubMap :: (TypeRep, SubMap f) -> [r]
        mapSubMap (_, SubMap m) = Prelude.map (uncurry f) $ M.toList m

-- | Apply a transformation to each value in the map.
map :: forall f. Typeable f =>
       (forall a. (TermEntry a, Show (f a), Eq (f a)) => f a -> f a) -> VarMap f -> VarMap f
map f (VarMap m) = VarMap $ M.map mapSubMap m
  where mapSubMap (SubMap sm) = SubMap $ M.map f sm

-- | Convert a 'VarMap' to a list of 'Entry' mappings. The order of the resulting list is undefined.
toList :: Typeable f => VarMap f -> [Entry f]
toList = collect Entry

-- | Create a 'VarMap' from a list of 'Entry' mappings.
fromList :: Typeable f => [Entry f] -> VarMap f
fromList = foldr insertOne empty
  where insertOne :: Typeable f => Entry f -> VarMap f -> VarMap f
        insertOne (Entry k v) = insert k v

-- | Executed a monadic action for each mapping in the table.
for :: forall f r m. (Typeable f, Monad m) =>
       VarMap f -> (forall a. (TermEntry a, Show (f a), Eq (f a)) => Var a -> f a -> m r) -> m [r]
for varMap f = sequence $ collect f varMap

-- | Traverse the table, executing a monadic action for its side-effects.
for_ :: forall f m. (Typeable f, Monad m) =>
        VarMap f -> (forall a. (TermEntry a, Show (f a), Eq (f a)) => Var a -> f a -> m ()) -> m ()
for_ varMap f = (for varMap f :: m [()]) >> return ()
