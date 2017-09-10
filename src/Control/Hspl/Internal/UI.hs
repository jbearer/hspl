{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.UI
Description : Formatting for user interactions via the CLI.
Stability   : Internal

The purpose of this module is to ensure that the internal representations of the various components
('Term's, 'Goal's, etc.) defined in "Control.Hspl.Internal.Ast" can be displayed in a manner
consistent with the syntax the user sees, as defined in "Control.Hspl". These functions should
always be kept up to date with the syntax defined in "Control.Hspl".
-}
module Control.Hspl.Internal.UI (
    formatType
  , parensType
  , formatVariable
  , parensVariable
  , formatTerm
  , parensTerm
  , formatGoal
  , parensGoal
  , formatPredicate
  , formatClause
  ) where

import Data.List
import Data.Typeable

import Control.Hspl.Internal.Ast

-- | Get a user-showable representation of a 'TypeRep'. If the type is a parameterized type, it is
-- /not/ wrapped in parentheses. To format a type where such a type should be enclosed in
-- parentheses, use 'parensType'.
formatType :: TypeRep -> String
formatType = show

-- | Similar to 'formatType', but if the type is a parameterized type (consisting of multiple
-- tokens) it will wrap the whole expression in parentheses.
parensType :: TypeRep -> String
parensType t =
  let str = formatType t
  in if ' ' `elem` str then "(" ++ str ++ ")" else str

-- | Get a user-showable representation of a 'Var'.
formatVariable :: TermEntry a => Var a -> String
formatVariable v = case v of
  Var x -> x ++ " :: " ++ formatType (varType v)
  Fresh i -> "_" ++ show i ++ " :: " ++ formatType (varType v)
  Anon -> "__ :: " ++ formatType (varType v)

-- | Similar to 'formatVariable', but 'parensVariable' will wrap the result in parentheses.
parensVariable :: TermEntry a => Var a -> String
parensVariable v = "(" ++ formatVariable v ++ ")"

-- | Get a user-showable representation of a 'Term'. Any subterms are wrapped in parentheses if
-- necessary so that the output is syntactically and semantically correct. However, the outer term
-- is unparenthesized. When formatting a term to use as a subexpression in a larger expression, use
-- 'parensTerm'.
formatTerm :: TermEntry a => Term a -> String
#ifdef SHOW_TERMS
formatTerm (Constant c) = show c
#else
formatTerm (Constant c) = "<" ++ formatType (typeOf c) ++ ">"
#endif

formatTerm (Variable v) = formatVariable v

formatTerm (Constructor c []) = show c
formatTerm (Constructor c [ETerm t]) = show c ++ " $$ " ++ parensTerm t
formatTerm (Constructor c t) =
  show c ++ " $$ (" ++ intercalate ", " (map (termMap formatTerm) t) ++ ")"

formatTerm (Tup tup) = "(" ++ joinTup tup ++ ")"
  where joinTup :: TupleTerm a -> String
        joinTup (Tuple2 t1 t2) = formatTerm t1 ++ ", " ++ formatTerm t2
        joinTup (TupleN t ts) = formatTerm t ++ ", " ++ joinTup ts

formatTerm term@(List list)
  | termType term == typeOf "" = case fromTerm term of
    Just str -> show str
    Nothing -> formatList list
  | otherwise = formatList list

  where formatList :: ListTerm a -> String
        formatList Nil = "[]"
        formatList l = case joinList l of
          (prefix, Nothing) -> "[" ++ prefix ++ "]"
          (prefix, Just rest) -> "[" ++ prefix ++ "] <++> " ++ rest

        -- Turn a list term into a comma-separated string. Return a tuple to handle partial lists.
        -- If the tail of the list is a variable, the second part of the tuple will be a string
        -- which must be appended to the list with <++>. Otherwise, it will be Nothing.
        joinList :: ListTerm a -> (String, Maybe String)
        joinList Nil = ("", Nothing)
        joinList (Cons t Nil) = (formatTerm t, Nothing)
        joinList (Cons t ts) =
          let (prefix, rest) = joinList ts
          in (formatTerm t ++ ", " ++ prefix, rest)
        joinList (VarCons t x) = (formatTerm t, Just $ parensVariable x)

formatTerm (Sum t1 t2) = parensTerm t1 ++ " |+| " ++ parensTerm t2
formatTerm (Difference t1 t2) = parensTerm t1 ++ " |-| " ++ parensTerm t2
formatTerm (Product t1 t2) = parensTerm t1 ++ " |*| " ++ parensTerm t2
formatTerm (Quotient t1 t2) = parensTerm t1 ++ " |/| " ++ parensTerm t2
formatTerm (IntQuotient t1 t2) = parensTerm t1 ++ " |\\| " ++ parensTerm t2
formatTerm (Modulus t1 t2) = parensTerm t1 ++ " |%| " ++ parensTerm t2

-- | Similar to 'formatTerm', but wraps the output in parentheses if it is not a single token.
parensTerm :: TermEntry a => Term a -> String
parensTerm t
  | needsParens t = "(" ++ formatTerm t ++ ")"
  | otherwise = formatTerm t
  where needsParens Constant {} = False
        needsParens Variable {} = True
        needsParens (Constructor _ []) = False
        needsParens (Constructor _ _) = True
        needsParens Tup {} = False
        needsParens List {} = False
        needsParens _ = True -- Arithmetic binary operators

-- | Get a user-showable representation of a 'Predicate'.
formatPredicate :: Predicate -> String
formatPredicate (Predicate name t) = name ++ "? " ++ parensTerm t

-- | Get a user-showable representation of a 'Goal'. Any subexpressions are wrapped in parentheses
-- if necessary so that the output is syntactically and semantically correct. However, the outer
-- goal is unparenthesized. When formatting a goal to use as a subexpression in a larger expression,
-- use 'parensGoal'.
formatGoal :: Goal -> String
formatGoal (PredGoal p _) = formatPredicate p
formatGoal (CanUnify t1 t2) = parensTerm t1 ++ " |=| " ++ parensTerm t2
formatGoal (Identical t1 t2) = parensTerm t1 ++ " `is` " ++ parensTerm t2
formatGoal (Equal t1 t2) = parensTerm t1 ++ " |==| " ++ parensTerm t2
formatGoal (LessThan t1 t2) = parensTerm t1 ++ " |<| " ++ parensTerm t2
formatGoal (IsUnified t) = "isUnified " ++ parensTerm t
formatGoal (IsVariable t) = "isVariable " ++ parensTerm t
formatGoal (Not g) = "lnot " ++ parensGoal g
formatGoal (And g1 g2) = parensGoal g1 ++ " >> " ++ parensGoal g2
formatGoal (Or g1 g2) = parensGoal g1 ++ " ||| " ++ parensGoal g2
formatGoal Top = "true"
formatGoal Bottom = "false"
formatGoal (Alternatives x g xs) =
  "findAll " ++ parensTerm x ++ " " ++ parensGoal g ++ " " ++ parensTerm xs
formatGoal (Once g) = "once " ++ parensGoal g
formatGoal Cut = "cut"

-- | Similar to 'formatGoal', but wraps the output in parentheses if it is not a single token.
parensGoal :: Goal -> String
parensGoal g
  | needsParens g = "(" ++ formatGoal g ++ ")"
  | otherwise = formatGoal g
  where needsParens Top = False
        needsParens Bottom = False
        needsParens Cut = False
        needsParens _ = True

-- | Get a user-showable representation of a 'HornClause'.
formatClause :: HornClause -> String
formatClause (HornClause (Predicate _ arg) Top) = "match " ++ parensTerm arg
formatClause (HornClause (Predicate _ arg) goal) =
  "match " ++ parensTerm arg ++ " |-" ++ (if needsDo goal then " do" else "") ++ "\n  " ++
    intercalate "\n  " (formatClauseGoal goal)
  where formatClauseGoal (And g1 g2) = formatClauseGoal g1 ++ formatClauseGoal g2
        formatClauseGoal g = [formatGoal g]
        needsDo And {} = True
        needsDo _ = False
