-- | λK₃ → λK₂ (spec/core.md §3): check the second-class reference rules, then translate
-- @&@ / @&mut@ parameters, @var@ locals and assignment into pure state passing.
--
-- A function @λ(&mut x:τ). e : &mut τ →ε σ@ becomes @λ(x:τ). e' : τ →ε σ ⊗ τ@: it returns its
-- result paired with the final value of @x@, and every call site rebinds @x@ to that value.
-- Assignment @x := e@ binds a fresh version of @x@. The result is checked by the λK₂ checker,
-- so linearity of places is enforced on the elaborated program.
module Keel.Elab (checkRefs, elaborate, checkSurface) where

import Control.Monad (forM_, when)
import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import Data.Map.Strict qualified as M
import Keel.Check (ErrKind (..), TypeError (..), checkProgram)
import Keel.Syntax

-- | Place-check, elaborate and type-check a λK₃ program.
checkSurface :: Program -> Either TypeError (Ty, Eff)
checkSurface p = checkRefs p >> checkProgram (elaborate p)

-- Place checking (§3.2) -------------------------------------------------------------------

data Access
  = Mutable   -- ^ @&mut@ parameter or @var@
  | ReadOnly  -- ^ @&@ parameter
  | Frozen    -- ^ outer place inside a handled expression: readable only
  | Captured  -- ^ outer place inside a closure or handler clause: inaccessible
  deriving (Eq)

type TC = Either TypeError

err :: ErrKind -> String -> TC a
err k msg = Left (TypeError k msg)

checkRefs :: Program -> TC ()
checkRefs (Program decls main) = do
  forM_ decls $ \d -> case d of
    Data _ _ _ cs -> mapM_ tyOk (concatMap snd cs)
    Codata _ _ os -> mapM_ (tyOk . snd) os
    Effect _ ops -> forM_ ops $ \(_, a, r) -> tyOk a >> tyOk r
    Def _ t e -> tyOk t >> places M.empty e
    Bitdata {} -> pure () -- removed by inference
  places M.empty main

-- | References may appear only as the parameter type of an arrow.
tyOk :: Ty -> TC ()
tyOk t = case t of
  TRef _ -> err RefEscape ("reference type outside a parameter: " ++ show t)
  TMut _ -> err RefEscape ("reference type outside a parameter: " ++ show t)
  TFun a _ b -> paramOk a >> tyOk b
  TLFun a _ b -> paramOk a >> tyOk b
  TBox a -> tyOk a
  TPair a b -> tyOk a >> tyOk b
  TData _ as -> mapM_ tyOk as
  TForall _ _ b -> tyOk b
  _ -> pure ()

paramOk :: Ty -> TC ()
paramOk t = case t of
  TRef a -> tyOk a
  TMut a -> tyOk a
  _ -> tyOk t

places :: M.Map String Access -> Term -> TC ()
places env tm = case tm of
  Var x -> readable x
  Assign x e -> writable x >> places env e
  App f (Borrow x) -> readable x >> rebindable x >> places env f
  App f (BorrowMut x) -> writable x >> places env f
  Borrow x -> err RefEscape ("&" ++ x ++ " is only allowed as a function argument")
  BorrowMut x -> err RefEscape ("&mut " ++ x ++ " is only allowed as a function argument")
  Lam x t b -> paramOk t >> places (enter x t) b
  LLam x t b -> paramOk t >> places (enter x t) b
  LetVar x e b -> places env e >> places (M.insert x Mutable env) b
  Handle _ b cs -> do
    places (M.map freeze env) b
    forM_ cs $ \(_, _, c) -> places (M.map (const Captured) env) c
  Cocase _ _ bs -> forM_ bs $ \(_, b) -> places (M.map (const Captured) env) b
  _ -> mapM_ (places env) (children tm)
  where
    enter x t =
      let outer = M.map (const Captured) env
       in case t of
            TMut _ -> M.insert x Mutable outer
            TRef _ -> M.insert x ReadOnly outer
            _ -> outer
    freeze a = if a == Captured then Captured else Frozen
    readable x = when (M.lookup x env == Just Captured) $ err PlaceCapture (x ++ " is a place from outside this closure")
    writable x = case M.lookup x env of
      Nothing -> err NotAPlace (x ++ " is not a &mut parameter or var")
      Just Captured -> err PlaceCapture (x ++ " is a place from outside this closure")
      Just Frozen -> err PlaceCapture (x ++ " can't be changed inside a handled expression")
      Just ReadOnly -> err NotMutable (x ++ " is a read-only (&) parameter")
      Just Mutable -> pure ()
    -- &x passes x and gets it back (§3.3), so x must be a place this code may rebind.
    rebindable x = case M.lookup x env of
      Nothing -> err NotAPlace (x ++ " is not a parameter or var")
      Just Frozen -> err PlaceCapture (x ++ " can't be borrowed inside a handled expression")
      _ -> pure ()

-- Elaboration (§3.3) ----------------------------------------------------------------------

type M = State Int

-- | Fresh names contain @#@, which source names never do.
fresh :: String -> M String
fresh base = do
  n <- get
  put (n + 1)
  pure (base ++ "#" ++ show n)

-- | Current name of each place in scope.
type Places = M.Map String String

-- | Continuation: the rest of the computation, given the updated places and a term for the
-- value. The value term is consumed before any further code is emitted.
type K = Places -> Term -> M Term

elaborate :: Program -> Program
elaborate (Program decls main) = evalState (Program <$> mapM decl decls <*> top main) 0
  where
    decl d = case d of
      Data l n ps cs -> pure (Data l n ps [(c, map elabTy fs) | (c, fs) <- cs])
      Codata n ps os -> pure (Codata n ps [(o, elabTy ty) | (o, ty) <- os])
      Effect l ops -> pure (Effect l [(op, elabTy a, elabTy r) | (op, a, r) <- ops])
      Def f t e -> Def f (elabTy t) <$> top e
      Bitdata {} -> pure d
    top e = expr M.empty e (\_ v -> pure v)

-- | @&τ →ε σ@ and @&mut τ →ε σ@ both become @τ →ε σ ⊗ τ@.
elabTy :: Ty -> Ty
elabTy t = case t of
  TFun a e b -> arrow TFun a e b
  TLFun a e b -> arrow TLFun a e b
  TBox a -> TBox (elabTy a)
  TPair a b -> TPair (elabTy a) (elabTy b)
  TData d as -> TData d (map elabTy as)
  TForall vs es b -> TForall vs es (elabTy b)
  TRef a -> elabTy a
  TMut a -> elabTy a
  _ -> t
  where
    arrow k a e b
      | isRef a = k (elabTy a) e (TPair (elabTy b) (elabTy a))
      | otherwise = k (elabTy a) e (elabTy b)

isRef :: Ty -> Bool
isRef (TRef _) = True
isRef (TMut _) = True
isRef _ = False

hasRef :: Ty -> Bool
hasRef t = case t of
  TRef _ -> True
  TMut _ -> True
  TFun a _ b -> hasRef a || hasRef b
  TLFun a _ b -> hasRef a || hasRef b
  TBox a -> hasRef a
  TPair a b -> hasRef a || hasRef b
  TData _ as -> any hasRef as
  TForall _ _ b -> hasRef b
  _ -> False

-- | Does the term need elaboration? Terms that don't are core already (up to renaming places).
usesRefs :: Term -> Bool
usesRefs tm = case tm of
  Assign {} -> True
  Seq {} -> True
  LetVar {} -> True
  Borrow _ -> True
  BorrowMut _ -> True
  Lam _ t b -> hasRef t || usesRefs b
  LLam _ t b -> hasRef t || usesRefs b
  _ -> any usesRefs (children tm)

-- | Replace reads of places with their current names.
rename :: Places -> Term -> Term
rename ps (Var x) = Var (M.findWithDefault x x ps)
rename ps tm = descend (rename ps) tm

expr :: Places -> Term -> K -> M Term
expr ps tm k
  | not (usesRefs tm) = k ps (rename ps tm)
  | otherwise = case tm of
      Assign x e -> expr ps e $ \ps1 v -> do
        x' <- fresh x
        Let x' v <$> k (M.insert x x' ps1) UnitLit
      Seq a b -> expr ps a $ \ps1 v -> do
        u <- fresh "seq"
        Let u v <$> expr ps1 b k
      LetVar x e b -> expr ps e $ \ps1 v -> do
        x' <- fresh x
        Let x' v <$> expr (M.insert x x' ps1) b (\ps2 -> k (M.delete x ps2))
      Let x e b -> expr ps e $ \ps1 v -> Let x v <$> expr ps1 b k
      App f (Borrow x) -> call f x
      App f (BorrowMut x) -> call f x
      App f a -> exprs ps [f, a] $ \ps1 vs -> k ps1 (foldl1 App vs)
      Lam x t b -> lam Lam x t b
      LLam x t b -> lam LLam x t b
      Prim op a b -> exprs ps [a, b] $ \ps1 vs -> case vs of
        [va, vb] -> k ps1 (Prim op va vb)
        _ -> error "unreachable"
      Con c tys as -> exprs ps as $ \ps1 vs -> k ps1 (Con c (map elabTy tys) vs)
      -- Like closures: branches see no outer places.
      Cocase d tys bs -> do
        bs' <- mapM (\(o, b) -> (o,) <$> expr M.empty b (\_ v -> pure v)) bs
        k ps (Cocase d (map elabTy tys) bs')
      Proj e o -> expr ps e $ \ps1 v -> k ps1 (Proj v o)
      Pair a b -> exprs ps [a, b] $ \ps1 vs -> case vs of
        [va, vb] -> k ps1 (Pair va vb)
        _ -> error "unreachable"
      Box e -> expr ps e $ \ps1 v -> k ps1 (Box v)
      Unbox e -> expr ps e $ \ps1 v -> k ps1 (Unbox v)
      Perform op e -> expr ps e $ \ps1 v -> k ps1 (Perform op v)
      LetPair x y e b -> expr ps e $ \ps1 v -> LetPair x y v <$> expr ps1 b k
      -- ponytail: the continuation is copied into both branches, so nested branches that
      -- mutate grow the output exponentially; join points (a local λ) fix that if it matters.
      If c a b -> expr ps c $ \ps1 vc -> If vc <$> expr ps1 a k <*> expr ps1 b k
      Case e alts -> expr ps e $ \ps1 ve ->
        Case ve <$> mapM (\(c, xs, b) -> (c,xs,) <$> expr ps1 b k) alts
      -- The handled expression only reads outer places (§3.2), so their names don't change.
      Handle l b cs -> do
        b' <- expr ps b (\_ v -> pure v)
        cs' <- mapM (\(op, x, c) -> (op,x,) <$> expr M.empty c (\_ v -> pure v)) cs
        k ps (Handle l b' cs')
      _ -> k ps (rename ps tm)
  where
    -- f(&x) or f(&mut x): pass x, get (result, new x) back.
    call f x = expr ps f $ \ps1 vf -> do
      r <- fresh "r"
      x' <- fresh x
      LetPair r x' (App vf (Var (M.findWithDefault x x ps1))) <$> k (M.insert x x' ps1) (Var r)

    -- A closure starts with no places except its own reference parameter.
    lam mk x t b = do
      body <-
        if isRef t
          then expr (M.singleton x x) b (\ps1 v -> pure (Pair v (Var (M.findWithDefault x x ps1))))
          else expr M.empty b (\_ v -> pure v)
      k ps (mk x (elabTy t) body)

-- | Elaborate terms left to right. A value is let-bound when a later term needs elaboration,
-- so it is evaluated before that term's emitted code (call-by-value order).
exprs :: Places -> [Term] -> (Places -> [Term] -> M Term) -> M Term
exprs ps [] k = k ps []
exprs ps (t : ts) k = expr ps t $ \ps1 v ->
  if any usesRefs ts
    then do
      a <- fresh "a"
      Let a v <$> exprs ps1 ts (\ps2 vs -> k ps2 (Var a : vs))
    else exprs ps1 ts (\ps2 vs -> k ps2 (v : vs))
