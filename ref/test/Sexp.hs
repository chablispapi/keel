-- | keelc's parse of a module as S-expressions, one top-level item per line: the format the
-- self-hosted parser (selfhost/parse.kl) prints, so the two can be compared.
module Sexp (sexpModule) where

import Data.Set qualified as S
import Keel.Syntax

sexpModule :: Module -> String
sexpModule (Module imports decls main _) =
  unlines $
    [list ["import", m, q] | (m, q, _) <- imports]
      ++ [if p then list ["private", decl d] else decl d | (p, d) <- decls]
      ++ [list ["main", term e] | Just e <- [main]]

list :: [String] -> String
list xs = "(" ++ unwords xs ++ ")"

decl :: Decl -> String
decl d = case d of
  Data lin n ps cs -> list ([if lin then "linear-data" else "data", n, list ps] ++ [list (c : map ty ts) | (c, ts) <- cs])
  Codata n ps os -> list (["codata", n, list ps] ++ [list [o, ty t] | (o, t) <- os])
  Effect n ops -> list (["effect", n] ++ [list [o, ty a, ty b] | (o, a, b) <- ops])
  Def f t e -> list ["def", f, ty t, term e]
  Bitdata n it fs -> list (["bitdata", n, intTy it] ++ [list [f, show lo, show w] | (f, lo, w) <- fs])

intTy :: IntTy -> String
intTy (IntTy s n) = (if s then "i" else "u") ++ show n

ty :: Ty -> String
ty t = case t of
  TUnit -> "Unit"
  TBool -> "Bool"
  TInt it -> intTy it
  TFun a e b -> list ["->", ty a, list (S.toList e), ty b]
  TLFun a e b -> list ["-o", ty a, list (S.toList e), ty b]
  TData n [] -> n
  TData n ts -> list (n : map ty ts)
  TVar v -> v
  TBox a -> list ["Box", ty a]
  TPair a b -> list [",", ty a, ty b]
  TForall vs es a -> list ["forall", list [list [v, show k] | (v, k) <- vs], list es, ty a]
  TRef a -> list ["&", ty a]
  TMut a -> list ["&mut", ty a]
  TMeta _ -> "_"

term :: Term -> String
term tm = case tm of
  Var x -> x
  UnitLit -> "()"
  IntLit it n -> list ["int", intTy it, show n]
  NumLit _ n -> show n
  Convert it e -> list ["as", intTy it, term e]
  BoolLit b -> if b then "true" else "false"
  Prim p a b -> list [prim p, term a, term b]
  ArrayPrim {} -> error "the parser makes no array primitives"
  If c a b -> list ["if", term c, term a, term b]
  Lam x t b -> list ["\\", x, ty t, term b]
  LLam x t b -> list ["\\o", x, ty t, term b]
  App f a -> list ["app", term f, term a]
  Let x e b -> list ["let", x, term e, term b]
  Con c ts as -> list (["con", c, list (map ty ts)] ++ map term as)
  Case e alts -> list (["case", term e] ++ [list [c, list xs, term b] | (c, xs, b) <- alts])
  Box e -> list ["box", term e]
  Unbox e -> list ["unbox", term e]
  Perform o e -> list ["perform", o, term e]
  Handle l e cs -> list (["handle", l, term e] ++ [list [o, x, term b] | (o, x, b) <- cs])
  Pair a b -> list ["pair", term a, term b]
  LetPair x y e b -> list ["letpair", x, y, term e, term b]
  TyApp f ts _ -> list ["tyapp", f, list (map ty ts)]
  Cocase d ts bs -> list (["cocase", d, list (map ty ts)] ++ [list [o, term b] | (o, b) <- bs])
  Proj e o -> list ["proj", term e, o]
  Assign x e -> list [":=", x, term e]
  Seq a b -> list ["seq", term a, term b]
  LetVar x e b -> list ["var", x, term e, term b]
  Borrow x -> list ["&", x]
  BorrowMut x -> list ["&mut", x]
  BitsLit c fs -> list (["bits", c] ++ [list [f, term e] | (f, e) <- fs])
  At _ e -> term e

prim :: Prim -> String
prim p = case p of
  Arith ov op -> base op ++ suffix ov
  Bits b -> case b of And -> "land"; Or -> "lor"; Xor -> "lxor"; Shl -> "lsl"; Shr -> "lsr"
  Eq -> "=="
  Lt -> "<"
  where
    base op = case op of Add -> "+"; Sub -> "-"; Mul -> "*"; Div -> "/"; Rem -> "%"
    suffix ov = case ov of Checked -> ""; Wrap -> "%"; Saturate -> "|"; Optional -> "?"
