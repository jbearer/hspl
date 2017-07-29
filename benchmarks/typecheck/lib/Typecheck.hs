{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Typecheck where

import Control.Hspl

import Data.Data
import GHC.Generics

data Type = IntType
          | BoolType
          | FuncType Type Type
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Type

data Op = Negate | Not
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Op

data BOp = Plus | Minus | Times | Divide | And | Or
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable BOp

data Expr = IntLiteral Int
          | BoolLiteral Bool
          | Variable String
          | Lambda String Expr
          | App Expr Expr
          | Let String Expr Expr
          | If Expr Expr Expr
          | PreOp Op Expr
          | BinOp Expr BOp Expr
  deriving (Show, Eq, Typeable, Data, Generic)
instance Termable Expr

type Env = [(String, Type)]

env :: String -> Var Env
env = Var

wellTypedWithEnv :: Predicate (Env, Expr, Type)
wellTypedWithEnv = predicate "wellTyped" $ do
  match (v"env", Variable $$ v"x", v"t") |- helem? ((v"x", v"t"), env "env")

  match (v"env", IntLiteral $$ v"x", IntType)
  match (v"env", BoolLiteral $$ v"b", BoolType)

  match (v"env", Lambda $$ (v"x", v"expr"), FuncType $$ (v"arg", v"result")) |-
    wellTypedWithEnv? ((v"x", v"arg") <:> v"env", v"expr", v"result")

  match (v"env", App $$ (v"f", v"x"), v"type") |- do
    wellTypedWithEnv? (v"env", v"f", FuncType $$ (v"arg", v"type"))
    wellTypedWithEnv? (v"env", v"x", v"arg")

  match (v"env", Let $$ (v"x", v"letExpr", v"inExpr"), v"type") |- do
    wellTypedWithEnv? (v"env", v"letExpr", v"letType")
    wellTypedWithEnv? ((v"x", v"letType") <:> v"env", v"inExpr", v"type")

  match (v"env", If $$ (v"cond", v"ifTrue", v"ifFalse"), v"type") |- do
    wellTypedWithEnv? (v"env", v"cond", BoolType)
    wellTypedWithEnv? (v"env", v"ifTrue", v"type")
    wellTypedWithEnv? (v"env", v"ifFalse", v"type")

  match (v"env", PreOp $$ (Negate, v"expr"), IntType) |-
    wellTypedWithEnv? (v"env", v"expr", IntType)
  match (v"env", PreOp $$ (Not, v"expr"), BoolType) |-
    wellTypedWithEnv? (v"env", v"expr", BoolType)

  match (v"env", BinOp $$ (v"l", v"op", v"r"), IntType) |- do
    helem? (v"op", [Plus, Minus, Times, Divide])
    wellTypedWithEnv? (v"env", v"l", IntType)
    wellTypedWithEnv? (v"env", v"r", IntType)
  match (v"env", BinOp $$ (v"l", v"op", v"r"), BoolType) |- do
    helem? (v"op", [And, Or])
    wellTypedWithEnv? (v"env", v"l", BoolType)
    wellTypedWithEnv? (v"env", v"r", BoolType)

wellTyped :: Predicate (Expr, Type)
wellTyped = predicate "wellTyped" $
  match (v"expr", v"type") |- wellTypedWithEnv? (nil, v"expr", v"type")

-- Code generators, so we can construct large examples

nestedInt :: Int -> Expr -> Expr -> Expr
nestedInt depth l r
  | depth <= 1 = BinOp l Minus r
  | otherwise = let subExpr = nestedInt (depth - 1) l r
                in BinOp subExpr op subExpr
  where op = case depth `mod` 4 of
               0 -> Plus
               1 -> Minus
               2 -> Times
               3 -> Divide

nestedBool :: Int -> Expr -> Expr -> Expr
nestedBool depth l r
  | depth <= 1 = BinOp l Or r
  | otherwise = let subExpr = nestedBool (depth - 1) l r
                in BinOp subExpr op subExpr
  where op = case depth `mod` 2 of
               0 -> And
               1 -> Or

nestedIf :: Int -> Expr -> Expr -> Expr -> Expr
nestedIf depth cond ifTrue ifFalse
  | depth <= 1 = If cond ifTrue ifFalse
  | otherwise = let subExpr = nestedIf (depth - 1) cond ifTrue ifFalse
                in If cond subExpr subExpr

nestedLetInt :: Int -> Expr -> Expr -> Expr
nestedLetInt depth letExpr inExpr
  | depth <= 1 = Let var letExpr (BinOp (Variable var) Plus inExpr)
  | otherwise = let subExpr = nestedLetInt (depth - 1) letExpr inExpr
                in Let var subExpr (BinOp (Variable var) Plus subExpr)
  where var = "nestedLetVar" ++ show depth

nestedLambdaInt :: Int -> Expr -> Expr
nestedLambdaInt depth expr
  | depth <= 1 = Lambda var (BinOp (Variable var) Plus expr)
  | otherwise = let subExpr = nestedLambdaInt (depth - 1) (BinOp (Variable var) Plus expr)
                in Lambda var subExpr
  where var = "nestedLambdaVar" ++ show depth

nestedAppInt :: Int -> Expr -> Expr -> Expr
nestedAppInt depth f arg
  | depth <= 1 = App f arg
  | otherwise = let f' = apply $ depth - 1
                in App f' (App f' arg)
  where apply n
          | n <= 1 = App f arg
          | otherwise = App (apply $ n - 1) arg

-- Examples
wellTypedInt :: Expr
wellTypedInt =
  let size = 3
      boolExpr = nestedBool size (PreOp Not $ BoolLiteral True) (PreOp Not $ BoolLiteral False)
      intExpr = nestedInt size (PreOp Negate $ IntLiteral 1) (PreOp Negate $ IntLiteral 2)
      ifExpr = nestedIf size boolExpr intExpr (PreOp Negate intExpr)
      letExpr = nestedLetInt size ifExpr ifExpr
  in nestedAppInt size (nestedLambdaInt size ifExpr) letExpr
