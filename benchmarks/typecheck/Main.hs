{-# LANGUAGE CPP #-}

import Bench
import Typecheck
import Control.Hspl
import Control.Monad
import Data.Maybe

main = compareTo (takeDirectory __FILE__ </> "lib" </> "typecheck.pl") $ do
  proofs <- bench "wellTypedInt" $ wellTyped? (wellTypedInt, v"type") >> v"type" |=| IntType
  when (isJust proofs) $ do
    let us = fromJust proofs
    assertEquals 1 (length us)
    assertEquals (Unified IntType) (queryVar (head us) (v"type"))
