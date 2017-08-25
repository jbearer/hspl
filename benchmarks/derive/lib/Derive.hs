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
d = semiDetPredicate "d" $ do
  match (Sum $$ (v"u", v"v"), v"x", Sum $$ (v"du", v"dv")) |- do
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Difference $$ (v"u", v"v"), v"x", Difference $$ (v"du", v"dv")) |- do
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Product $$ (v"u", v"v"), v"x",
         Sum $$ (Product $$ (v"du", v"v"), Product $$ (v"u", v"dv"))) |- do
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Quotient $$ (v"u", v"v"), v"x",
         Quotient $$ ( Difference $$ (Product $$ (v"du", v"v"), Product $$ (v"u", v"dv"))
                     , Power $$ (v"v", 2 :: Int))) |- do
    d? (v"u", v"x", v"du")
    d? (v"v", v"x", v"dv")

  match (Power $$ (v"u", v"n"), v"x",
         Product $$ (v"du", Product $$ (v"n", Power $$ (v"u", v"n1")))) |- do
    v"n1" |==| v"n" |-| (1 :: Int)
    d? (v"u", v"x", v"du")

  match (Exp $$ v"u", v"x", Product $$ (v"du", Exp $$ v"u")) |-
    d? (v"u", v"x", v"du")

  match (Log $$ v"u", v"x", Quotient $$ (v"du", v"u")) |-
    d? (v"u", v"x", v"du")

  match (Var $$ v"x", v"x", Const 1)
  match (Var $$ v"x", v"y", Const 0) |-
    int "x" |\=| v"y"

  match(Const $$ v"n", v"x", Const 0)

binOps :: Expr
binOps = Product (Sum (Var "x") (Const 1))
                 (Product (Sum (Power (Var "x") 2) (Const 2))
                          (Sum (Power (Var "x") 3) (Const 3)))

dBinOps :: Expr
dBinOps = Sum (Product (Sum (Const 1) (Const 0)) (Product (Sum (Power (Var "x") 2) (Const 2))
                                                          (Sum (Power (Var "x") 3) (Const 3))))
              (Product (Sum (Var "x") (Const 1))
                       (Sum (Product (Sum (Product (Const 1)
                                                   (Product (Const 2) (Power (Var "x") 1)))
                                          (Const 0))
                                     (Sum (Power (Var "x") 3) (Const 3)))
                            (Product (Sum (Power (Var "x") 2) (Const 2))
                                     (Sum (Product (Const 1)
                                                   (Product (Const 3) (Power (Var "x") 2)))
                                          (Const 0)))))

nestedLogs :: Int -> Expr
nestedLogs n
  | n == 0 = Var "x"
  | otherwise = Log $ nestedLogs (n - 1)

dNestedLogs :: Int -> Expr
dNestedLogs n
  | n == 0 = Const 1
  | otherwise = Quotient (dNestedLogs $ n - 1) (nestedLogs $ n - 1)
