{-# LANGUAGE BangPatterns #-}

-- | Call-by-value, environment-based evaluator for Keel Core, stage 1 (spec/core.md §1.4).
-- Assumes a well-typed program; stuck states are impossible by Theorem 1.
module Keel.Eval (Value (..), evalProgram) where

import Data.Map.Strict qualified as M
import Keel.Syntax

data Value
  = VInt Integer
  | VBool Bool
  | VClo Env String Term -- ^ ⟨ρ, x, e⟩, for both λ and λ° (linearity is erased)
  | VCon String [Value]
  | VBox Value

type Env = M.Map String Value

instance Show Value where
  show v = case v of
    VInt n -> show n
    VBool b -> if b then "true" else "false"
    VClo {} -> "<closure>"
    VCon c [] -> c
    VCon c vs -> c ++ "(" ++ commas (map show vs) ++ ")"
    VBox a -> "box " ++ show a
    where
      commas = foldr1 (\a b -> a ++ ", " ++ b)

-- | Structural equality on first-order values; closures are never equal.
instance Eq Value where
  VInt a == VInt b = a == b
  VBool a == VBool b = a == b
  VCon c vs == VCon d ws = c == d && vs == ws
  VBox a == VBox b = a == b
  _ == _ = False

evalProgram :: Program -> Value
evalProgram (Program decls main) = eval globals main
  where
    -- ρ_Σ: the recursive knot of top-level definitions.
    globals = M.fromList [(f, eval globals e) | Def f _ e <- decls]

-- | Values are forced before they are bound or stored, so evaluation order is CBV even though
-- the host language is lazy. Only the global knot is left lazy.
eval :: Env -> Term -> Value
eval env tm = case tm of
  Var x -> env M.! x
  IntLit n -> VInt n
  BoolLit b -> VBool b
  Prim op a b ->
    let !va = eval env a
        !vb = eval env b
     in prim op va vb
  If c a b -> case eval env c of
    VBool True -> eval env a
    _ -> eval env b
  Lam x _ body -> VClo env x body
  LLam x _ body -> VClo env x body
  App f a ->
    let !vf = eval env f
        !va = eval env a
     in case vf of
          VClo cenv x body -> eval (M.insert x va cenv) body
          _ -> stuck "application of a non-closure"
  Let x e body ->
    let !v = eval env e
     in eval (M.insert x v env) body
  Con c args ->
    let vs = map (eval env) args
     in foldr seq (VCon c vs) vs
  Case e alts -> case eval env e of
    VCon c vs
      | (xs, body) : _ <- [(xs, body) | (c', xs, body) <- alts, c' == c] ->
          eval (M.union (M.fromList (zip xs vs)) env) body
    _ -> stuck "case without a matching constructor"
  Box e -> let !v = eval env e in VBox v
  Unbox e -> case eval env e of
    VBox v -> v
    _ -> stuck "unbox of a non-box"

prim :: Prim -> Value -> Value -> Value
prim op (VInt a) (VInt b) = case op of
  Add -> VInt (a + b)
  Sub -> VInt (a - b)
  Mul -> VInt (a * b)
  Eq -> VBool (a == b)
  Lt -> VBool (a < b)
prim _ _ _ = stuck "primitive on non-integers"

stuck :: String -> a
stuck msg = error ("stuck (ill-typed program?): " ++ msg)
