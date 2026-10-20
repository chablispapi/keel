-- | Algorithmic type checker for Keel Core, stages 1–3 (spec/core.md §1.2–1.3, §2.2–2.4, §3.2).
-- It checks the core; λK₃ programs are first place-checked and elaborated by "Keel.Elab".
--
-- @infer@ implements Γ ⊢ e ⇒ τ ! ε ▷ U: it synthesizes a type, the effect of evaluating the
-- term, and the set U of linear local variables the term uses.
module Keel.Check (ErrKind (..), TypeError (..), checkProgram) where

import Control.Monad (foldM, forM, forM_, unless, when)
import Data.List (nub, sort)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Syntax

data ErrKind
  = Mismatch
  | EffectMismatch
  | Unbound
  | Shadowing
  | Duplicate
  | Dropped
  | BranchMismatch
  | LinearCapture
  | LinearField
  | InfiniteSize
  | NonPositive
  | NonExhaustive
  | Unhandled
  | BadDecl
  | RefEscape    -- ^ a reference outside a parameter type or function argument (§3)
  | NotAPlace    -- ^ assigning to or borrowing something that isn't a place
  | NotMutable   -- ^ assigning to or &mut-borrowing a read-only place
  | PlaceCapture -- ^ a closure or handler reaching a place from outside
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
  , sigEffs :: M.Map String [(String, Ty, Ty)]       -- ^ handleable effect ↦ operations
  , sigOps :: M.Map String (String, Ty, Ty)          -- ^ operation ↦ (label, argument, result)
  }

builtinEffects :: [(String, [(String, Ty, Ty)])]
builtinEffects = [(ioE, [("out", TInt i64, TUnit)])]

-- | Effects @main@ may leave unhandled: the machine provides them.
topLevelEffects :: Eff
topLevelEffects = S.fromList [ioE, panicE, divergeE]

kindOf :: Sig -> Ty -> Kind
kindOf s t = case t of
  TLFun {} -> Lin
  TBox a -> kindOf s a
  TPair a b | kindOf s a == Lin || kindOf s b == Lin -> Lin
  TData d | Just (True, _) <- M.lookup d (sigData s) -> Lin
  _ -> Free

-- | Subtyping (§2.3): fewer effects is better, and a free function is also a linear one.
sub :: Ty -> Ty -> Bool
sub a b = case (a, b) of
  (TFun p e r, TFun p' e' r') -> fn p e r p' e' r'
  (TFun p e r, TLFun p' e' r') -> fn p e r p' e' r'
  (TLFun p e r, TLFun p' e' r') -> fn p e r p' e' r'
  (TBox x, TBox y) -> sub x y
  (TPair x y, TPair x' y') -> sub x x' && sub y y'
  _ -> a == b
  where
    fn p e r p' e' r' = sub p' p && e `S.isSubsetOf` e' && sub r r'

eraseEff :: Ty -> Ty
eraseEff t = case t of
  TFun p _ r -> TFun (eraseEff p) S.empty (eraseEff r)
  TLFun p _ r -> TLFun (eraseEff p) S.empty (eraseEff r)
  TBox a -> TBox (eraseEff a)
  TPair a b -> TPair (eraseEff a) (eraseEff b)
  _ -> t

-- | Report @got@ not fitting @expected@, separating effect-only differences.
mismatch :: Ty -> Ty -> TC a
mismatch expected got
  | sub (eraseEff got) (eraseEff expected) = err EffectMismatch msg
  | otherwise = err Mismatch msg
  where
    msg = "expected " ++ show expected ++ ", got " ++ show got

type Ctx = M.Map String Ty

type Usage = S.Set String

-- | Check a whole program; returns the type and effect of @main@.
checkProgram :: Program -> TC (Ty, Eff)
checkProgram (Program decls main) = do
  sig <- buildSig decls
  let defs = [(f, t, e) | Def f t e <- decls]
      refs = M.fromList [(f, globalsIn (sigDefs sig) e) | (f, _, e) <- defs]
      reach = M.fromList [(f, reachable refs f) | (f, _, _) <- defs]
      scc f = S.filter (\g -> f `S.member` (reach M.! g)) (reach M.! f)
  forM_ defs $ \(f, t, e) -> do
    wfTy sig t
    (t', eff, _) <- infer sig (scc f) M.empty e
    unless (S.null eff) $ err Unhandled ("def " ++ f ++ " has effects " ++ show (S.toList eff))
    unless (sub t' t) $ mismatch t t'
  (t, eff, _) <- infer sig S.empty M.empty main
  let extra = eff S.\\ topLevelEffects
  unless (S.null extra) $ err Unhandled ("main performs " ++ show (S.toList extra))
  pure (t, eff)

-- | Global names referenced by a term. Locals never share names with globals (no shadowing).
globalsIn :: M.Map String Ty -> Term -> S.Set String
globalsIn defs = go
  where
    go (Var x) = if M.member x defs then S.singleton x else S.empty
    go tm = foldMap go (children tm)

-- | Names reachable in one or more steps.
reachable :: M.Map String (S.Set String) -> String -> S.Set String
reachable refs f0 = go S.empty (next f0)
  where
    next f = S.toList (M.findWithDefault S.empty f refs)
    go seen [] = seen
    go seen (f : fs)
      | f `S.member` seen = go seen fs
      | otherwise = go (S.insert f seen) (next f ++ fs)

buildSig :: [Decl] -> TC Sig
buildSig decls = do
  let datas = [(d, (lin, cs)) | Data lin d cs <- decls]
      cons = [(c, (fs, d)) | (d, (_, cs)) <- datas, (c, fs) <- cs]
      defs = [(f, t) | Def f t _ <- decls]
      effs = builtinEffects ++ [(l, os) | Effect l os <- decls]
      ops = [(op, (l, a, r)) | (l, os) <- effs, (op, a, r) <- os]
      labels = map fst effs ++ [panicE, divergeE]
      names xs = map fst xs
  forM_ [("data", names datas), ("constructor", names cons), ("def", names defs), ("effect", labels), ("operation", names ops)] $
    \(what, ns) -> when (length ns /= length (nub ns)) $ err BadDecl ("duplicate " ++ what ++ " name")
  let sig = Sig (M.fromList datas) (M.fromList cons) (M.fromList defs) (M.fromList effs) (M.fromList ops)
  forM_ ops $ \(_, (_, a, r)) -> wfTy sig a >> wfTy sig r
  forM_ datas $ \(d, (lin, cs)) -> forM_ cs $ \(c, fs) -> forM_ fs $ \f -> do
    wfTy sig f
    when (not lin && kindOf sig f == Lin) $
      err LinearField (d ++ "." ++ c ++ " has a linear field but " ++ d ++ " is not linear")
  forM_ (names datas) $ \d -> do
    when (d `S.member` reachUnboxed sig d) $ err InfiniteSize (d ++ " contains itself without Box")
    when (occursNegatively sig d) $ err NonPositive (d ++ " occurs to the left of an arrow in its own definition")
  pure sig

fieldsOf :: Sig -> String -> [Ty]
fieldsOf s d = [f | Just (_, cs) <- [M.lookup d (sigData s)], (_, fs) <- cs, f <- fs]

-- | Data types stored inline (not behind Box or a function) in a type.
unboxedData :: Ty -> [String]
unboxedData t = case t of
  TData d -> [d]
  TPair a b -> unboxedData a ++ unboxedData b
  _ -> []

-- | Data types reachable from @d@ through unboxed fields (well-formedness rule 2).
reachUnboxed :: Sig -> String -> S.Set String
reachUnboxed s d0 = go S.empty (direct d0)
  where
    direct d = concatMap unboxedData (fieldsOf s d)
    go seen [] = seen
    go seen (d : ds)
      | d `S.member` seen = go seen ds
      | otherwise = go (S.insert d seen) (direct d ++ ds)

-- | Strict positivity (well-formedness rule 4): @d@ never appears left of an arrow inside
-- itself, following other data types transitively.
occursNegatively :: Sig -> String -> Bool
occursNegatively s d = any (walk S.empty True) (fieldsOf s d)
  where
    walk seen pos t = case t of
      TFun a _ b -> walk seen (not pos) a || walk seen pos b
      TLFun a _ b -> walk seen (not pos) a || walk seen pos b
      TBox a -> walk seen pos a
      TPair a b -> walk seen pos a || walk seen pos b
      TData d'
        | d' == d -> not pos
        | (d', pos) `S.member` seen -> False
        | otherwise -> any (walk (S.insert (d', pos) seen) pos) (fieldsOf s d')
      _ -> False

wfTy :: Sig -> Ty -> TC ()
wfTy s t = case t of
  TFun a e b -> wfEff e >> wfTy s a >> wfTy s b
  TLFun a e b -> wfEff e >> wfTy s a >> wfTy s b
  TBox a -> wfTy s a
  TPair a b -> wfTy s a >> wfTy s b
  TRef _ -> err RefEscape "reference type in core (elaborate first)"
  TMut _ -> err RefEscape "reference type in core (elaborate first)"
  TData d -> unless (M.member d (sigData s)) $ err Unbound ("type " ++ d)
  _ -> pure ()
  where
    wfEff e = forM_ e $ \l ->
      unless (M.member l (sigEffs s) || l `elem` [panicE, divergeE]) $ err Unbound ("effect " ++ l)

-- | @rec@ is the recursive group of the definition being checked: referencing one of its
-- members has the effect Diverge (§2.4).
infer :: Sig -> S.Set String -> Ctx -> Term -> TC (Ty, Eff, Usage)
infer s rec ctx tm = case tm of
  Var x -> case M.lookup x ctx of
    Just t -> pure (t, S.empty, if kindOf s t == Lin then S.singleton x else S.empty)
    Nothing -> case M.lookup x (sigDefs s) of
      Just t -> pure (t, if x `S.member` rec then S.singleton divergeE else S.empty, S.empty)
      Nothing -> err Unbound x
  UnitLit -> pure (TUnit, S.empty, S.empty)
  IntLit it n -> do
    let (lo, hi) = intRange it
    unless (n >= lo && n <= hi) $ err Mismatch (show n ++ " does not fit " ++ show it)
    pure (TInt it, S.empty, S.empty)
  BoolLit _ -> pure (TBool, S.empty, S.empty)
  Prim op a b -> do
    (ta, ea, ua) <- infer s rec ctx a
    case ta of
      TInt _ -> pure ()
      _ -> err Mismatch ("arithmetic on " ++ show ta)
    (eb, ub) <- expect ta b
    u <- join2 ua ub
    let panics = case op of
          Arith Checked _ -> S.singleton panicE
          _ -> S.empty
        t = if op `elem` [Eq, Lt] then TBool else ta
    pure (t, S.unions [ea, eb, panics], u)
  If c a b -> do
    (ec, uc) <- expect TBool c
    (ta, ea, ua) <- infer s rec ctx a
    (eb, ub) <- expect ta b
    unless (ua == ub) $ err BranchMismatch (branches ua ub)
    (ta,S.unions [ec, ea, eb],) <$> join2 uc ua
  Lam x t body -> do
    (tb, eb, u) <- bind [(x, t)] body
    unless (S.null u) $ err LinearCapture ("free λ" ++ x ++ " captures " ++ show (S.toList u))
    pure (TFun t eb tb, S.empty, u)
  LLam x t body -> do
    (tb, eb, u) <- bind [(x, t)] body
    pure (TLFun t eb tb, S.empty, u)
  App f a -> do
    (tf, ef, uf) <- infer s rec ctx f
    (p, latent, r) <- case tf of
      TFun p e r -> pure (p, e, r)
      TLFun p e r -> pure (p, e, r)
      _ -> err Mismatch ("applying a non-function of type " ++ show tf)
    (ea, ua) <- expect p a
    (r,S.unions [ef, ea, latent],) <$> join2 uf ua
  Let x e body -> do
    (te, ee, ue) <- infer s rec ctx e
    (tb, eb, ub) <- bind [(x, te)] body
    (tb,ee <> eb,) <$> join2 ue ub
  Con c args -> do
    (fields, d) <- maybe (err Unbound ("constructor " ++ c)) pure (M.lookup c (sigCons s))
    when (length fields /= length args) $ err Mismatch (c ++ ": wrong number of fields")
    rs <- mapM (uncurry expect) (zip fields args)
    u <- foldM join2 S.empty (map snd rs)
    pure (TData d, S.unions (map fst rs), u)
  Case e alts -> do
    (te, ee, ue) <- infer s rec ctx e
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
      (t, _, u) : rest -> do
        forM_ rest $ \(t', _, u') -> do
          unless (t' == t) $ err Mismatch ("case branches have types " ++ show t ++ " and " ++ show t')
          unless (u' == u) $ err BranchMismatch (branches u u')
        (t,S.unions (ee : [e' | (_, e', _) <- rs]),) <$> join2 ue u
  Box e -> do
    (t, eff, u) <- infer s rec ctx e
    pure (TBox t, eff, u)
  Unbox e -> do
    (t, eff, u) <- infer s rec ctx e
    case t of
      TBox a -> pure (a, eff, u)
      _ -> err Mismatch ("unbox of non-Box type " ++ show t)
  Perform op a -> do
    (l, targ, tres) <- maybe (err Unbound ("operation " ++ op)) pure (M.lookup op (sigOps s))
    (ea, ua) <- expect targ a
    pure (tres, S.insert l ea, ua)
  Handle l body clauses -> do
    ops <- maybe (err Unbound ("effect " ++ l ++ " cannot be handled")) pure (M.lookup l (sigEffs s))
    unless (sort [op | (op, _, _) <- clauses] == sort [op | (op, _, _) <- ops]) $
      err NonExhaustive ("handler for " ++ l ++ " must handle each operation exactly once")
    (tb, eb, ub) <- infer s rec ctx body
    ecs <- forM clauses $ \(op, x, e) -> do
      -- present: clause names checked against ops above
      let (targ, tres) = fromMaybe (TUnit, TUnit) (lookup op [(op', (a, r)) | (op', a, r) <- ops])
      (tc, ec, uc) <- bind [(x, targ)] e
      unless (S.null uc) $ err LinearCapture ("handler clause " ++ op ++ " captures " ++ show (S.toList uc))
      unless (sub tc tres) $ mismatch tres tc
      pure ec
    pure (tb, S.unions (S.delete l eb : ecs), ub)
  Pair a b -> do
    (ta, ea, ua) <- infer s rec ctx a
    (tb, eb, ub) <- infer s rec ctx b
    (TPair ta tb,ea <> eb,) <$> join2 ua ub
  LetPair x y e body -> do
    (te, ee, ue) <- infer s rec ctx e
    (ta, tb) <- case te of
      TPair ta tb -> pure (ta, tb)
      _ -> err Mismatch ("let-pair of non-pair type " ++ show te)
    (tr, eb, ub) <- bind [(x, ta), (y, tb)] body
    (tr,ee <> eb,) <$> join2 ue ub
  _ -> err RefEscape ("surface construct in core (elaborate first): " ++ show tm)
  where
    expect t e = do
      (t', eff, u) <- infer s rec ctx e
      unless (sub t' t) $ mismatch t t'
      pure (eff, u)

    -- Binders: no shadowing, and every linear binder must be used in the body.
    bind xts body = do
      forM_ xts $ \(x, _) ->
        when (M.member x ctx || M.member x (sigDefs s)) $ err Shadowing x
      when (length xts /= length (nub (map fst xts))) $ err Shadowing "repeated pattern variable"
      (tb, eff, u) <- infer s rec (M.union (M.fromList xts) ctx) body
      forM_ xts $ \(x, t) ->
        when (kindOf s t == Lin && not (x `S.member` u)) $ err Dropped (x ++ " is linear but unused")
      pure (tb, eff, u `S.difference` S.fromList (map fst xts))

    -- Two subterms evaluated together: their linear usage must be disjoint.
    join2 a b =
      let both = S.intersection a b
       in if S.null both then pure (S.union a b) else err Duplicate (show (S.toList both) ++ " used twice")

    branches a b = "branches use " ++ show (S.toList a) ++ " and " ++ show (S.toList b)
