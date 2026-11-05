-- | Structural termination (spec/core.md §2.4): a recursive group whose every recursion is on
-- a structurally smaller argument terminates, so references to its members don't have the
-- effect Diverge. This is the structural part of Agda's termination checker (Abel, "foetus",
-- 1998), without lexicographic orders or size-change graphs.
--
-- Each member f gets one parameter position i_f. The group terminates when, for some choice
-- of positions, every reference to a member g inside a member f is a call
-- @g a₀ … aₙ@ with n ≥ i_g whose argument a_{i_g} is a variable bound, by @case@ (or @unbox@
-- of one), inside f's parameter i_f: a part of it, so a smaller value. Data values are finite
-- (no laziness, no cycles), and strict positivity rules out a loop without a recursive
-- definition, so every chain of such calls is finite. A reference that isn't such a call
-- (passing f along, @twice f k@) keeps the group diverging.
module Keel.Termination (terminatingGroups) where

import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Syntax

-- | The recursive groups, with every group that provably terminates made empty.
terminatingGroups :: [Decl] -> M.Map String (S.Set String) -> M.Map String (S.Set String)
terminatingGroups decls groups = M.map (\g -> if g `S.member` total then S.empty else g) groups
  where
    defs = M.fromList [(f, e) | Def f _ e <- decls]
    total = S.fromList [g | g <- S.toList (S.fromList (M.elems groups)), not (S.null g), terminates g]
    terminates g =
      let members = S.toList g
          arity f = length (fst (params (fromMaybe UnitLit (M.lookup f defs))))
          -- ponytail: tries every choice of positions; a group with more than 4096 stays diverging.
          choices = sequence [[(f, i) | i <- [0 .. arity f - 1]] | f <- members]
       in product (map arity members) <= 4096 && any (\c -> all (decreases g (M.fromList c)) members) choices
    decreases g idx f =
      let (ps, body) = params (fromMaybe UnitLit (M.lookup f defs))
          env = Env (M.fromList [(p, Just (False, k)) | (k, p) <- zip [0 ..] ps]) M.empty (assigned body)
       in walk g idx (idx M.! f) env body

-- | Every local variable, and what it is: a parameter or a part of one (Just (True, k): a part
-- of parameter k), or another name for a group member (in eFuns).
data Env = Env {eVals :: M.Map String (Maybe (Bool, Int)), eFuns :: M.Map String String, eAssigned :: S.Set String}

-- | A definition's parameters (its leading λs) and body.
params :: Term -> ([String], Term)
params tm = case tm of
  At _ e -> params e
  Lam x _ b -> let (ps, e) = params b in (x : ps, e)
  LLam x _ b -> let (ps, e) = params b in (x : ps, e)
  _ -> ([], tm)

-- | Variables assigned anywhere: their value can change, so they are never tracked.
assigned :: Term -> S.Set String
assigned tm = S.fromList [x | Assign x _ <- universe tm]

-- | Is every reference to a member of g, in tm, a call on a part of parameter self?
walk :: S.Set String -> M.Map String Int -> Int -> Env -> Term -> Bool
walk g idx self env tm = case tm of
  At _ e -> go env e
  App {}
    | (h, args) <- spine tm, Just callee <- member h ->
        all (go env) args && case drop (idx M.! callee) args of
          a : _ -> partOf a
          [] -> False
  Var x -> isNothing' (member (Var x))
  TyApp f _ _ -> f `S.notMember` g
  -- let x = g (the elaborator names a function before its effectful arguments)
  Let x e b | Just callee <- member e -> go (bindFun x callee env) b
  Let x e b -> go env e && go (bind x (valueOf e) env) b
  LetVar x e b -> go env e && go (bind x Nothing env) b
  LetPair x y e b -> go env e && go (bind y Nothing (bind x Nothing env)) b
  Lam x _ b -> go (bind x Nothing env) b
  LLam x _ b -> go (bind x Nothing env) b
  Case s alts ->
    go env s && and [go (foldr (\x -> bind x (fields s)) env xs) b | (_, xs, b) <- alts]
  Handle _ e cs -> go env e && and [go (bind x Nothing env) b | (_, x, b) <- cs]
  _ -> all (go env) (children tm)
  where
    go = walk g idx self
    member h = case h of
      At _ e -> member e
      Var x | x `S.member` g, M.notMember x (eVals env) -> Just x
      Var x -> M.lookup x (eFuns env)
      TyApp f _ _ | f `S.member` g -> Just f
      _ -> Nothing
    isNothing' = maybe True (const False)
    -- A parameter or a part of one, through @unbox@ and positions.
    valueOf e = case e of
      At _ e' -> valueOf e'
      Unbox e' -> valueOf e'
      Var x -> M.findWithDefault Nothing x (eVals env)
      _ -> Nothing
    -- The fields of a case on a parameter or a part of one are parts of it.
    fields s = (\(_, k) -> (True, k)) <$> valueOf s
    partOf a = valueOf a == Just (True, self)
    bind x v e = e {eVals = M.insert x (if x `S.member` eAssigned e then Nothing else v) (eVals e), eFuns = M.delete x (eFuns e)}
    bindFun x f e = (bind x Nothing e) {eFuns = M.insert x f (eFuns e)}

spine :: Term -> (Term, [Term])
spine tm = case tm of
  At _ e -> spine e
  App f a -> let (h, as) = spine f in (h, as ++ [a])
  _ -> (tm, [])
