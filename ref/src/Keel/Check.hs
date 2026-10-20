-- | Algorithmic type checker for Keel Core, stage 1 (spec/core.md §1.2–1.3).
--
-- @infer@ implements the judgment Γ ⊢ e ⇒ τ ▷ U: it synthesizes a type together with the
-- set U of linear local variables the term uses. Linearity errors come from the usage rules.
module Keel.Check (ErrKind (..), TypeError (..), checkProgram) where

import Control.Monad (foldM, forM, forM_, unless, when, zipWithM)
import Data.List (nub, sort)
import Data.Maybe (fromMaybe)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.Syntax

data ErrKind
  = Mismatch
  | Unbound
  | Shadowing
  | Duplicate
  | Dropped
  | BranchMismatch
  | LinearCapture
  | LinearField
  | InfiniteSize
  | NonExhaustive
  | BadDecl
  deriving (Eq, Show)

data TypeError = TypeError ErrKind String
  deriving (Eq, Show)

type TC = Either TypeError

err :: ErrKind -> String -> TC a
err k msg = Left (TypeError k msg)

-- | The signature Σ.
data Sig = Sig
  { sigData :: M.Map String (Bool, [(String, [Ty])]) -- ^ data name ↦ (linear?, constructors)
  , sigCons :: M.Map String ([Ty], String)           -- ^ constructor ↦ (field types, data name)
  , sigDefs :: M.Map String Ty
  }

kindOf :: Sig -> Ty -> Kind
kindOf s t = case t of
  TLFun _ _ -> Lin
  TBox a -> kindOf s a
  TData d | Just (True, _) <- M.lookup d (sigData s) -> Lin
  _ -> Free

type Ctx = M.Map String Ty

type Usage = S.Set String

-- | Check a whole program; returns the type of @main@.
checkProgram :: Program -> TC Ty
checkProgram (Program decls main) = do
  sig <- buildSig decls
  forM_ [(f, t, e) | Def f t e <- decls] $ \(f, t, e) -> do
    wfTy sig t
    (t', _) <- infer sig M.empty e
    unless (t == t') $ err Mismatch ("def " ++ f ++ ": declared " ++ show t ++ ", body " ++ show t')
  fst <$> infer sig M.empty main

buildSig :: [Decl] -> TC Sig
buildSig decls = do
  let datas = [(d, (lin, cs)) | Data lin d cs <- decls]
      cons = [(c, (fs, d)) | (d, (_, cs)) <- datas, (c, fs) <- cs]
      defs = [(f, t) | Def f t _ <- decls]
      names xs = map fst xs
  forM_ [("data", names datas), ("constructor", names cons), ("def", names defs)] $ \(what, ns) ->
    when (length ns /= length (nub ns)) $ err BadDecl ("duplicate " ++ what ++ " name")
  let sig = Sig (M.fromList datas) (M.fromList cons) (M.fromList defs)
  forM_ datas $ \(d, (lin, cs)) -> forM_ cs $ \(c, fs) -> forM_ fs $ \f -> do
    wfTy sig f
    when (not lin && kindOf sig f == Lin) $
      err LinearField (d ++ "." ++ c ++ " has a linear field but " ++ d ++ " is not linear")
  forM_ (names datas) $ \d ->
    when (d `S.member` reachUnboxed sig d) $ err InfiniteSize (d ++ " contains itself without Box")
  pure sig

-- | Data types reachable from @d@ through unboxed fields (well-formedness rule 2).
reachUnboxed :: Sig -> String -> S.Set String
reachUnboxed s d0 = go S.empty (direct d0)
  where
    direct d = [d' | Just (_, cs) <- [M.lookup d (sigData s)], (_, fs) <- cs, TData d' <- fs]
    go seen [] = seen
    go seen (d : ds)
      | d `S.member` seen = go seen ds
      | otherwise = go (S.insert d seen) (direct d ++ ds)

wfTy :: Sig -> Ty -> TC ()
wfTy s t = case t of
  TFun a b -> wfTy s a >> wfTy s b
  TLFun a b -> wfTy s a >> wfTy s b
  TBox a -> wfTy s a
  TData d -> unless (M.member d (sigData s)) $ err Unbound ("type " ++ d)
  _ -> pure ()

infer :: Sig -> Ctx -> Term -> TC (Ty, Usage)
infer s ctx tm = case tm of
  Var x -> case M.lookup x ctx of
    Just t -> pure (t, if kindOf s t == Lin then S.singleton x else S.empty)
    Nothing -> maybe (err Unbound x) (\t -> pure (t, S.empty)) (M.lookup x (sigDefs s))
  IntLit _ -> pure (TInt, S.empty)
  BoolLit _ -> pure (TBool, S.empty)
  Prim op a b -> do
    ua <- expect TInt a
    ub <- expect TInt b
    (if op `elem` [Eq, Lt] then TBool else TInt,) <$> join2 ua ub
  If c a b -> do
    uc <- expect TBool c
    (ta, ua) <- infer s ctx a
    ub <- expect ta b
    unless (ua == ub) $ err BranchMismatch (branches ua ub)
    (ta,) <$> join2 uc ua
  Lam x t body -> do
    (tb, u) <- bind [(x, t)] body
    unless (S.null u) $ err LinearCapture ("free λ" ++ x ++ " captures " ++ show (S.toList u))
    pure (TFun t tb, u)
  LLam x t body -> do
    (tb, u) <- bind [(x, t)] body
    pure (TLFun t tb, u)
  App f a -> do
    (tf, uf) <- infer s ctx f
    (targ, tres) <- case tf of
      TFun p r -> pure (p, r)
      TLFun p r -> pure (p, r)
      _ -> err Mismatch ("applying a non-function of type " ++ show tf)
    ua <- expect targ a
    (tres,) <$> join2 uf ua
  Let x e body -> do
    (te, ue) <- infer s ctx e
    (tb, ub) <- bind [(x, te)] body
    (tb,) <$> join2 ue ub
  Con c args -> do
    (fields, d) <- maybe (err Unbound ("constructor " ++ c)) pure (M.lookup c (sigCons s))
    when (length fields /= length args) $ err Mismatch (c ++ ": wrong number of fields")
    us <- zipWithM expect fields args
    (TData d,) <$> foldM join2 S.empty us
  Case e alts -> do
    (te, ue) <- infer s ctx e
    ctors <- case te of
      TData d -> pure (snd (sigData s M.! d))
      _ -> err Mismatch ("case on non-data type " ++ show te)
    unless (sort [c | (c, _, _) <- alts] == sort (map fst ctors)) $
      err NonExhaustive ("case must match each of " ++ show (map fst ctors) ++ " exactly once")
    rs <- forM alts $ \(c, xs, body) -> do
      let fields = fromMaybe [] (lookup c ctors) -- present: checked against ctors above
      when (length xs /= length fields) $ err Mismatch (c ++ ": wrong number of pattern variables")
      bind (zip xs fields) body
    case rs of
      [] -> err NonExhaustive "empty case"
      (t, u) : rest -> do
        forM_ rest $ \(t', u') -> do
          unless (t' == t) $ err Mismatch ("case branches have types " ++ show t ++ " and " ++ show t')
          unless (u' == u) $ err BranchMismatch (branches u u')
        (t,) <$> join2 ue u
  Box e -> do
    (t, u) <- infer s ctx e
    pure (TBox t, u)
  Unbox e -> do
    (t, u) <- infer s ctx e
    case t of
      TBox a -> pure (a, u)
      _ -> err Mismatch ("unbox of non-Box type " ++ show t)
  where
    expect t e = do
      (t', u) <- infer s ctx e
      unless (t == t') $ err Mismatch ("expected " ++ show t ++ ", got " ++ show t')
      pure u

    -- Binders: no shadowing, and every linear binder must be used in the body.
    bind xts body = do
      forM_ xts $ \(x, _) ->
        when (M.member x ctx || M.member x (sigDefs s)) $ err Shadowing x
      when (length xts /= length (nub (map fst xts))) $ err Shadowing "repeated pattern variable"
      (tb, u) <- infer s (M.union (M.fromList xts) ctx) body
      forM_ xts $ \(x, t) ->
        when (kindOf s t == Lin && not (x `S.member` u)) $ err Dropped (x ++ " is linear but unused")
      pure (tb, u `S.difference` S.fromList (map fst xts))

    -- Two subterms evaluated together: their linear usage must be disjoint.
    join2 a b =
      let both = S.intersection a b
       in if S.null both then pure (S.union a b) else err Duplicate (show (S.toList both) ++ " used twice")

    branches a b = "branches use " ++ show (S.toList a) ++ " and " ++ show (S.toList b)
