{-# LANGUAGE CPP #-}

import Bench
import PseudoPerfect
import Control.Hspl
import Control.Monad
import Data.Maybe

goal = findAll (int "c") (perfect? v"c") (v"xs") .&. v"xs" .=. expected

main = compareTo (takeDirectory __FILE__ </> "lib" </> "pseudo-perfect.pl") $ do
  proofs <- bench "pseudoPerfect" goal
  when (isJust proofs) $ do
    let us = fromJust proofs
    assertEquals 1 (length us)
    assertEquals (Unified expected) (queryVar (head us) (v"xs"))
