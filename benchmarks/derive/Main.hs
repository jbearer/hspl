{-# LANGUAGE CPP #-}

import Bench
import Derive
import Control.Hspl
import Control.Monad
import Data.Maybe

main = compareTo (takeDirectory __FILE__ </> "lib" </> "derive.pl") $ do
  proofs <- bench "binOps" $ d? (binOps, "x", v"d") >> v"d" |=| dBinOps
  when (isJust proofs) $ do
    let us = getAllUnifiers $ fromJust proofs
    assertEquals 1 (length us)
    assertEquals (Unified dBinOps) (queryVar (head us) (v"d"))

  proofs <- bench "nestedLogs" $ d? (nestedLogs 1000, "x", v"d") >> v"d" |=| dNestedLogs 1000
  when (isJust proofs) $ do
    let us = getAllUnifiers $ fromJust proofs
    assertEquals 1 (length us)
    assertEquals (Unified $ dNestedLogs 1000) (queryVar (head us) (v"d"))
