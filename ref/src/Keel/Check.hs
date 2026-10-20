-- | Algorithmic type checker for Keel Core, stages 1–4 (spec/core.md §1.2–1.3, §2.2–2.4,
-- §3.2, §4.2–4.3). It checks the core; λK₃ programs are first place-checked and elaborated by
-- "Keel.Elab".
--
-- @infer@ implements Γ ⊢ e ⇒ τ ! ε ▷ U: it synthesizes a type, the effect of evaluating the
-- term, and the set U of linear local variables the term uses.
module Keel.Check (ErrKind (..), TypeError (..), checkProgram, recursiveGroups) where

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
  | RefEscape     -- ^ a reference outside a parameter type or function argument (§3)
  | NotAPlace     -- ^ assigning to or borrowing something that isn't a place
  | NotMutable    -- ^ assigning to or &mut-borrowing a read-only place
  | PlaceCapture  -- ^ a closure or handler reaching a place from outside
  | KindMismatch  -- ^ a linear type given for a Free type variable (§4)
  | HigherRank    -- ^ ∀ anywhere but the top of a def's type
  | PolyRecursion -- ^ a recursive group calling itself at different types (§4.4)
  deriving (Eq, Show)

data TypeError = TypeError ErrKind String
  deriving (Eq, Show)

type TC = Either TypeError

err :: ErrKind -> String -> TC a
err k msg = Left (TypeError k msg)

-- | The signature Σ, plus the type and effect variables in scope.
data Sig = Sig
  { sigData :: M.Map String (Bool, [String], [(String, [Ty])]) -- ^ data ↦ (linear?, params, constructors)
  , sigCons :: M.Map String ([Ty], String)                     -- ^ constructor ↦ (field types, data name)
  , sigCodata :: M.Map String ([String], [(String, Ty)])       -- ^ codata ↦ (params, observations)
  , sigDefs :: M.Map String Ty
  , sigEffs :: M.Map String [(String, Ty, Ty)]                 -- ^ handleable effect ↦ operations
  , sigOps :: M.Map String (String, Ty, Ty)                    -- ^ operation ↦ (label, argument, result)
  , sigTv :: M.Map String Kind                                 -- ^ type variables in scope
  , sigEv :: S.Set String                                      -- ^ effect variables in scope
  }

builtinEffects :: [(String, [(String, Ty, Ty)])]
builtinEffects = [(ioE, [("out", TInt i64, TUnit)])]

-- | Effects @main@ may leave unhandled: the machine provides them.
topLevelEffects :: Eff
topLevelEffects = S.fromList [ioE, panicE, divergeE]

-- | §1.2 and §4.2: a data type is linear if declared so or if any type argument is linear;
-- codata is always Free; a type variable has its declared kind.
kindOf :: Sig -> Ty -> Kind
kindOf s t = case t of
  TLFun {} -> Lin
  TBox a -> kindOf s a
  TPair a b | Lin `elem` [kindOf s a, kindOf s b] -> Lin
  TVar a -> M.findWithDefault Lin a (sigTv s)
  TData d as
    | Just (lin, _, _) <- M.lookup d (sigData s), lin || any ((== Lin) . kindOf s) as -> Lin
  _ -> Free

-- | Subtyping (§2.3): fewer effects is better, and a free function is also a linear one.
-- Type arguments of data and codata are invariant.
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
  TData d as -> TData d (map eraseEff as)
  _ -> t

-- | Report @got@ not fitting @expected@, separating effect-only differences.
mismatch :: Ty -> Ty -> TC a
mismatch expected got
  | sub (eraseEff got) (eraseEff expected) = err EffectMismatch msg
  | otherwise = err Mismatch msg
  where
    msg = "expected " ++ prettyTy expected ++ ", got " ++ prettyTy got

type Ctx = M.Map String Ty

type Usage = S.Set String

-- | Check a whole program; returns the type and effect of @main@.
checkProgram :: Program -> TC (Ty, Eff)
checkProgram (Program decls main) = do
  sig <- buildSig decls
  let groups = recursiveGroups decls
  forM_ [(f, t, e) | Def f t e <- decls] $ \(f, t, e) -> do
    let (vs, es, body) = case t of
          TForall vs' es' b -> (vs', es', b)
          _ -> ([], [], t)
        sig' = sig {sigTv = M.fromList vs, sigEv = S.fromList es}
    wfTy sig' body
    (t', eff, _) <- infer sig' (M.findWithDefault S.empty f groups) M.empty e
    unless (S.null eff) $ err Unhandled ("def " ++ f ++ " has effects " ++ prettyEff eff)
    unless (sub t' body) $ mismatch body t'
  (t, eff, _) <- infer sig S.empty M.empty main
  let extra = eff S.\\ topLevelEffects
  unless (S.null extra) $ err Unhandled ("main performs " ++ prettyEff extra)
  pure (t, eff)

-- | For each definition, its recursive group: the definitions it reaches that reach it back.
recursiveGroups :: [Decl] -> M.Map String (S.Set String)
recursiveGroups decls = M.fromList [(f, S.filter (\g -> f `S.member` (reach M.! g)) (reach M.! f)) | f <- names]
  where
    names = [f | Def f _ _ <- decls]
    defs = S.fromList names
    refs = M.fromList [(f, globalsIn defs e) | Def f _ e <- decls]
    reach = M.fromList [(f, reachable refs f) | f <- names]

-- | Global names referenced by a term. Locals never share names with globals (no shadowing).
globalsIn :: S.Set String -> Term -> S.Set String
globalsIn defs = go
  where
    go (Var x) = if x `S.member` defs then S.singleton x else S.empty
    go (TyApp f _ _) = S.singleton f
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
buildSig userDecls = do
  let decls = optionDecl : userDecls
      datas = [(d, (lin, ps, cs)) | Data lin d ps cs <- decls]
      codatas = [(d, (ps, os)) | Codata d ps os <- decls]
      cons = [(c, (fs, d)) | (d, (_, _, cs)) <- datas, (c, fs) <- cs]
      defs = [(f, t) | Def f t _ <- decls]
      effs = builtinEffects ++ [(l, os) | Effect l os <- decls]
      ops = [(op, (l, a, r)) | (l, os) <- effs, (op, a, r) <- os]
      labels = map fst effs ++ [panicE, divergeE]
      names xs = map fst xs
      unique what ns = when (length ns /= length (nub ns)) $ err BadDecl ("duplicate " ++ what ++ " name")
  unique "type" (names datas ++ names codatas)
  unique "constructor" (names cons)
  unique "def" (names defs)
  unique "effect" labels
  unique "operation" (names ops)
  forM_ codatas $ \(_, (_, os)) -> unique "observation" (names os)
  forM_ (map snd datas) $ \(_, ps, _) -> unique "type parameter" ps
  forM_ (map snd codatas) $ \(ps, _) -> unique "type parameter" ps
  let sig = Sig (M.fromList datas) (M.fromList cons) (M.fromList codatas) (M.fromList defs) (M.fromList effs) (M.fromList ops) M.empty S.empty
      -- Parameters count as Free inside their declaration: an argument's linearity
      -- propagates to the whole type instead (kindOf).
      inDecl ps = sig {sigTv = M.fromList [(p, Free) | p <- ps]}
  forM_ ops $ \(_, (_, a, r)) -> wfTy sig a >> wfTy sig r
  forM_ datas $ \(d, (lin, ps, cs)) -> forM_ cs $ \(c, fs) -> forM_ fs $ \f -> do
    wfTy (inDecl ps) f
    when (not lin && kindOf (inDecl ps) f == Lin) $
      err LinearField (d ++ "." ++ c ++ " has a linear field but " ++ d ++ " is not linear")
  forM_ codatas $ \(_, (ps, os)) -> forM_ os $ \(_, t) -> wfTy (inDecl ps) t
  let vm = variances sig
  forM_ (names datas) $ \d ->
    when (d `S.member` reachUnboxed sig d) $ err InfiniteSize (d ++ " contains itself without Box")
  forM_ (names datas ++ names codatas) $ \d ->
    when (occursNegatively sig vm d) $ err NonPositive (d ++ " occurs to the left of an arrow in its own definition")
  pure sig

-- | Field types of a data type, or observation types of a codata type, mentioning its parameters.
fieldsOf :: Sig -> String -> [Ty]
fieldsOf s d = case (M.lookup d (sigData s), M.lookup d (sigCodata s)) of
  (Just (_, _, cs), _) -> concatMap snd cs
  (_, Just (_, os)) -> map snd os
  _ -> []

paramsOf :: Sig -> String -> [String]
paramsOf s d = case (M.lookup d (sigData s), M.lookup d (sigCodata s)) of
  (Just (_, ps, _), _) -> ps
  (_, Just (ps, _)) -> ps
  _ -> []

-- | Data types stored inline (not behind Box, a function or codata) in a type. Type arguments
-- count as inline: conservative, since a parameter may be stored unboxed.
unboxedData :: Sig -> Ty -> [String]
unboxedData s t = case t of
  TData d as | M.member d (sigData s) -> d : concatMap (unboxedData s) as
  TPair a b -> unboxedData s a ++ unboxedData s b
  _ -> []

-- | Data types reachable from @d@ through unboxed fields (well-formedness rule 2).
reachUnboxed :: Sig -> String -> S.Set String
reachUnboxed s d0 = go S.empty (direct d0)
  where
    direct d = concatMap (unboxedData s) (fieldsOf s d)
    go seen [] = seen
    go seen (d : ds)
      | d `S.member` seen = go seen ds
      | otherwise = go (S.insert d seen) (direct d ++ ds)

-- | For every data and codata type, the polarities (True = positive) at which each of its
-- parameters occurs, as a least fixpoint over all declarations (§4.3).
variances :: Sig -> M.Map String [S.Set Bool]
variances s = fixp (M.fromList [(d, map (const S.empty) (paramsOf s d)) | d <- types])
  where
    types = M.keys (sigData s) ++ M.keys (sigCodata s)
    fixp vm = let vm' = step vm in if vm' == vm then vm else fixp vm'
    step vm =
      M.fromList
        [ (d, [S.fromList [pol | (p', pol) <- concatMap (occ vm True) (fieldsOf s d), p' == p] | p <- paramsOf s d])
        | d <- types
        ]
    occ vm pos t = case t of
      TVar a -> [(a, pos)]
      TFun a _ b -> occ vm (not pos) a ++ occ vm pos b
      TLFun a _ b -> occ vm (not pos) a ++ occ vm pos b
      TBox a -> occ vm pos a
      TPair a b -> occ vm pos a ++ occ vm pos b
      TData d as -> concat [occ vm (if q then pos else not pos) a | (a, qs) <- zip as (M.findWithDefault [] d vm), q <- S.toList qs]
      _ -> []

-- | Strict positivity (well-formedness rule 4): @d@ never appears left of an arrow in its own
-- definition, also through the parameters of other types.
occursNegatively :: Sig -> M.Map String [S.Set Bool] -> String -> Bool
occursNegatively s vm d = any (neg True) (fieldsOf s d)
  where
    neg pos t = case t of
      TFun a _ b -> neg (not pos) a || neg pos b
      TLFun a _ b -> neg (not pos) a || neg pos b
      TBox a -> neg pos a
      TPair a b -> neg pos a || neg pos b
      TData d' as ->
        (d' == d && not pos)
          || or [neg (if q then pos else not pos) a | (a, qs) <- zip as (M.findWithDefault [] d' vm), q <- S.toList qs]
      _ -> False

wfTy :: Sig -> Ty -> TC ()
wfTy s t = case t of
  TFun a e b -> wfEff s e >> wfTy s a >> wfTy s b
  TLFun a e b -> wfEff s e >> wfTy s a >> wfTy s b
  TBox a -> wfTy s a
  TPair a b -> wfTy s a >> wfTy s b
  TVar a -> unless (M.member a (sigTv s)) $ err Unbound ("type variable " ++ a)
  TData d as -> do
    unless (M.member d (sigData s) || M.member d (sigCodata s)) $ err Unbound ("type " ++ d)
    when (length as /= length (paramsOf s d)) $ err Mismatch (d ++ ": wrong number of type arguments")
    mapM_ (wfTy s) as
  TForall {} -> err HigherRank ("∀ is only allowed at the top of a definition's type: " ++ prettyTy t)
  TRef _ -> err RefEscape "reference type in core (elaborate first)"
  TMut _ -> err RefEscape "reference type in core (elaborate first)"
  _ -> pure ()

wfEff :: Sig -> Eff -> TC ()
wfEff s e = forM_ e $ \l ->
  unless (M.member l (sigEffs s) || l `elem` [panicE, divergeE] || l `S.member` sigEv s) $
    err Unbound ("effect " ++ l)

-- | @rec@ is the recursive group of the definition being checked: referencing one of its
-- members has the effect Diverge (§2.4).
infer :: Sig -> S.Set String -> Ctx -> Term -> TC (Ty, Eff, Usage)
infer s rec ctx tm = case tm of
  Var x -> case M.lookup x ctx of
    Just t -> pure (t, S.empty, if kindOf s t == Lin then S.singleton x else S.empty)
    Nothing -> case M.lookup x (sigDefs s) of
      Just TForall {} -> err Mismatch (x ++ " is polymorphic: apply it to types, " ++ x ++ "[…]")
      Just t -> pure (t, divergeIf x, S.empty)
      Nothing -> err Unbound x
  TyApp f tys effs -> do
    (vs, es, body) <- case M.lookup f (sigDefs s) of
      Just (TForall vs es body) -> pure (vs, es, body)
      Just _ -> err Mismatch (f ++ " is not polymorphic")
      Nothing -> err Unbound f
    when (length tys /= length vs || length effs /= length es) $
      err Mismatch (f ++ ": wrong number of type or effect arguments")
    forM_ (zip vs tys) $ \((v, k), ty) -> do
      wfTy s ty
      when (k == Free && kindOf s ty == Lin) $
        err KindMismatch (f ++ ": " ++ v ++ " must be Free, got linear " ++ prettyTy ty)
    mapM_ (wfEff s) effs
    pure (substTy (M.fromList (zip (map fst vs) tys)) (M.fromList (zip es effs)) body, divergeIf f, S.empty)
  UnitLit -> pure (TUnit, S.empty, S.empty)
  IntLit it n -> do
    let (lo, hi) = intRange it
    unless (n >= lo && n <= hi) $ err Mismatch (show n ++ " does not fit " ++ prettyTy (TInt it))
    pure (TInt it, S.empty, S.empty)
  BoolLit _ -> pure (TBool, S.empty, S.empty)
  Prim op a b -> do
    (ta, ea, ua) <- infer s rec ctx a
    case ta of
      TInt _ -> pure ()
      _ -> err Mismatch ("arithmetic on " ++ prettyTy ta)
    (eb, ub) <- expect ta b
    u <- join2 ua ub
    let (t, extra) = case op of
          Eq -> (TBool, S.empty)
          Lt -> (TBool, S.empty)
          Arith Checked _ -> (ta, S.singleton panicE)
          Arith Optional _ -> (TData "Option" [ta], S.empty)
          Arith _ _ -> (ta, S.empty)
    pure (t, S.unions [ea, eb, extra], u)
  If c a b -> do
    (ec, uc) <- expect TBool c
    (ta, ea, ua) <- infer s rec ctx a
    (eb, ub) <- expect ta b
    unless (ua == ub) $ err BranchMismatch (branches ua ub)
    (ta,S.unions [ec, ea, eb],) <$> join2 uc ua
  Lam x t body -> do
    wfTy s t
    (tb, eb, u) <- bind [(x, t)] body
    unless (S.null u) $ err LinearCapture ("free λ" ++ x ++ " captures " ++ show (S.toList u))
    pure (TFun t eb tb, S.empty, u)
  LLam x t body -> do
    wfTy s t
    (tb, eb, u) <- bind [(x, t)] body
    pure (TLFun t eb tb, S.empty, u)
  App f a -> do
    (tf, ef, uf) <- infer s rec ctx f
    (p, latent, r) <- case tf of
      TFun p e r -> pure (p, e, r)
      TLFun p e r -> pure (p, e, r)
      _ -> err Mismatch ("applying a non-function of type " ++ prettyTy tf)
    (ea, ua) <- expect p a
    (r,S.unions [ef, ea, latent],) <$> join2 uf ua
  Let x e body -> do
    (te, ee, ue) <- infer s rec ctx e
    (tb, eb, ub) <- bind [(x, te)] body
    (tb,ee <> eb,) <$> join2 ue ub
  Con c tys args -> do
    (fields, d) <- maybe (err Unbound ("constructor " ++ c)) pure (M.lookup c (sigCons s))
    let ps = paramsOf s d
    when (length tys /= length ps) $ err Mismatch (c ++ ": wrong number of type arguments")
    mapM_ (wfTy s) tys
    when (length fields /= length args) $ err Mismatch (c ++ ": wrong number of fields")
    let inst = substTy (M.fromList (zip ps tys)) M.empty
    rs <- mapM (uncurry expect) (zip (map inst fields) args)
    u <- foldM join2 S.empty (map snd rs)
    pure (TData d tys, S.unions (map fst rs), u)
  Case e alts -> do
    (te, ee, ue) <- infer s rec ctx e
    (ctors, inst) <- case te of
      TData d tys | Just (_, ps, cs) <- M.lookup d (sigData s) ->
        pure (cs, substTy (M.fromList (zip ps tys)) M.empty)
      _ -> err Mismatch ("case on non-data type " ++ prettyTy te)
    unless (sort [c | (c, _, _) <- alts] == sort (map fst ctors)) $
      err NonExhaustive ("case must match each of " ++ show (map fst ctors) ++ " exactly once")
    rs <- forM alts $ \(c, xs, body) -> do
      let fields = fromMaybe [] (lookup c ctors) -- present: checked against ctors above
      when (length xs /= length fields) $ err Mismatch (c ++ ": wrong number of pattern variables")
      bind (zip xs (map inst fields)) body
    case rs of
      [] -> err NonExhaustive "empty case"
      (t, _, u) : rest -> do
        forM_ rest $ \(t', _, u') -> do
          unless (t' == t) $ err Mismatch ("case branches have types " ++ prettyTy t ++ " and " ++ prettyTy t')
          unless (u' == u) $ err BranchMismatch (branches u u')
        (t,S.unions (ee : [e' | (_, e', _) <- rs]),) <$> join2 ue u
  Box e -> do
    (t, eff, u) <- infer s rec ctx e
    pure (TBox t, eff, u)
  Unbox e -> do
    (t, eff, u) <- infer s rec ctx e
    case t of
      TBox a -> pure (a, eff, u)
      _ -> err Mismatch ("unbox of non-Box type " ++ prettyTy t)
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
      _ -> err Mismatch ("let-pair of non-pair type " ++ prettyTy te)
    (tr, eb, ub) <- bind [(x, ta), (y, tb)] body
    (tr,ee <> eb,) <$> join2 ue ub
  Cocase d tys bs -> do
    (ps, obs) <- maybe (err Unbound ("codata " ++ d)) pure (M.lookup d (sigCodata s))
    when (length tys /= length ps) $ err Mismatch (d ++ ": wrong number of type arguments")
    mapM_ (wfTy s) tys
    unless (sort (map fst bs) == sort (map fst obs)) $
      err NonExhaustive ("cocase must define each of " ++ show (map fst obs) ++ " exactly once")
    let inst = substTy (M.fromList (zip ps tys)) M.empty
    forM_ bs $ \(o, e) -> do
      let want = inst (fromMaybe TUnit (lookup o obs)) -- present: checked against obs above
      (te, ee, ue) <- infer s rec ctx e
      unless (S.null ue) $ err LinearCapture ("cocase branch " ++ o ++ " captures " ++ show (S.toList ue))
      unless (S.null ee) $ err EffectMismatch ("cocase branch " ++ o ++ " has effects " ++ prettyEff ee)
      unless (sub te want) $ mismatch want te
    pure (TData d tys, S.empty, S.empty)
  Proj e o -> do
    (te, ee, ue) <- infer s rec ctx e
    case te of
      TData d tys
        | Just (ps, obs) <- M.lookup d (sigCodata s)
        , Just t <- lookup o obs ->
            pure (substTy (M.fromList (zip ps tys)) M.empty t, ee, ue)
      _ -> err Mismatch ("no observation " ++ o ++ " on " ++ prettyTy te)
  _ -> err RefEscape ("surface construct in core (elaborate first): " ++ show tm)
  where
    divergeIf x = if x `S.member` rec then S.singleton divergeE else S.empty

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
