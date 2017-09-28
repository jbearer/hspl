{-# LANGUAGE CPP #-}

import Bench
import Derive
import Control.Hspl
import Control.Monad
import Data.Maybe

benchExpr :: String -> Expr -> Benchmark ()
benchExpr name expr = do
  proofs <- bench name $ d? (expr, "x", v"d") .&. v"d" .=. trueD expr "x"
  when (isJust proofs) $ do
    let us = fromJust proofs
    assertEquals 1 (length us)
    assertEquals (Unified $ trueD expr "x") (queryVar (head us) (v"d"))

main = compareTo (takeDirectory __FILE__ </> "lib" </> "derive.pl") $ do
  benchExpr "binOps" $ binOps 20
  benchExpr "logs" $ logs 500
