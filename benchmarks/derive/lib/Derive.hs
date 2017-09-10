{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Derive where

import Control.Hspl hiding (Var)
import Data.Data
import GHC.Generics

data Expr = Sum Expr Expr
          | Product Expr Expr
          | Difference Expr Expr
          | Quotient Expr Expr
          | Power Expr Int
          | Exp Expr
          | Log Expr
          | Const Int
          | Var String
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Expr

d :: Predicate (Expr, String, Expr)
d = predicate "d" $ do
  match (Sum $$ (v"u", v"v"), v"x", Sum $$ (v"du", v"dv")) |- do
    cut
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Difference $$ (v"u", v"v"), v"x", Difference $$ (v"du", v"dv")) |- do
    cut
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Product $$ (v"u", v"v"), v"x",
         Sum $$ (Product $$ (v"du", v"v"), Product $$ (v"u", v"dv"))) |- do
    cut
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Quotient $$ (v"u", v"v"), v"x",
         Quotient $$ ( Difference $$ (Product $$ (v"du", v"v"), Product $$ (v"u", v"dv"))
                     , Power $$ (v"v", 2 :: Int))) |- do
    cut
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Power $$ (v"u", v"n"), v"x",
         Product $$ (v"du", Product $$ (Const $$ v"n", Power $$ (v"u", v"n1")))) |- do
    v"n1" |==| v"n" |-| (1 :: Int)
    cut
    d? (v"u", v"x", v"du")

  match (Exp $$ v"u", v"x", Product $$ (v"du", Exp $$ v"u")) |- do
    cut
    d? (v"u", v"x", v"du")

  match (Log $$ v"u", v"x", Quotient $$ (v"du", v"u")) |- do
    cut
    d? (v"u", v"x", v"du")

  match (Var $$ v"x", v"x", Const 1) |- cut
  match (Var $$ v"x", v"y", Const 0) |- do
    cut
    string "x" |\=| v"y"

  match(Const $$ __, __, Const 0)

-- | Clone of 'd' above, written in Haskell and therefore (presumable) correct. Used to check the
-- output of HSPL.
trueD :: Expr -> String -> Expr
trueD (Sum l r) x = Sum (trueD l x) (trueD r x)
trueD (Difference l r) x = Difference (trueD l x) (trueD r x)
trueD (Product l r) x = Sum (Product (trueD l x) r) (Product l (trueD r x))
trueD (Quotient n d) x = Quotient (Difference (Product (trueD n x) d) (Product n (trueD d x))) (Power d 2)
trueD (Power b p) x = Product (trueD b x) (Product (Const p) (Power b (p - 1)))
trueD (Exp p) x = Product (trueD p x) (Exp p)
trueD (Log u) x = Quotient (trueD u x) u
trueD (Var x) y
  | x == y = Const 1
  | otherwise = Const 0
trueD (Const n) _ = Const 0

binOps :: Int -> Expr
binOps n
  -- Leaves
  | n <= 1 = Sum (Var "x") (Const 1)
  | n == 2 = Product (Const 2) (Var "x")
  | n == 3 = Difference (Var "x") (Var "y")
  | n == 4 = Quotient (Var "y") (Var "x")
  -- Recursive expressions
  | n `mod` 4 == 1 = Sum (binOps $ n - 1) (binOps $ n - 2)
  | n `mod` 4 == 2 = Product (binOps $ n - 1) (binOps $ n - 2)
  | n `mod` 4 == 3 = Difference (binOps $ n - 1) (binOps $ n - 2)
  | n `mod` 4 == 0 = Quotient (binOps $ n - 1) (binOps $ n - 2)

logs :: Int -> Expr
logs n
  | n == 0 = Var "x"
  | otherwise = Log $ logs (n - 1)

