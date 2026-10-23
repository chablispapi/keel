-- | Type inference for the surface language (roadmap M1). Keel Core is explicitly typed; the
-- surface lets you leave out what can be inferred:
--
-- * λ parameter types (holes, @TMeta (-1)@) when the λ is checked against a known type or
--   its parameter is used at a known type;
-- * integer literal widths (default i64);
-- * type arguments of constructors, cocases and polymorphic definitions, and effect
--   arguments of polymorphic definitions;
-- * whether a λ is linear (λ°): it is when it captures a linear value;
-- * operations are written like calls, @read(4)@, and become @Perform@;
-- * @bitdata@ types: distinct types while checking, plain integers in the output; @s.field@
--   reads a bit field, @s.raw@ the whole value, @Status(x)@ and @Status { f = e, … }@ build one.
--
-- Binders may shadow: they are renamed apart (@x~1@), since the core forbids shadowing.
--
-- Inference only fills in annotations; the result is then checked by the core pipeline
-- ("Keel.Mono".compile), which gives the authoritative errors. Types are solved by
-- unification; an effect variable is solved by the union of the effects flowing into it.
module Keel.Infer (inferProgram, freeVars) where

import Control.Monad (forM, forM_, unless, when, zipWithM, zipWithM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT (..), evalStateT, get, gets, modify, put)
import Data.List (isPrefixOf)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.Check (ErrKind (..), TypeError (..), atPos, recursiveGroups)
import Keel.Syntax

data Sig = Sig
  { sData :: M.Map String (Bool, [String], [(String, [Ty])])
  , sCons :: M.Map String (String, [Ty]) -- ^ constructor ↦ (data name, field types)
  , sCodata :: M.Map String ([String], [(String, Ty)])
  , sDefs :: M.Map String Ty
  , sOps :: M.Map String (String, Ty, Ty) -- ^ operation ↦ (label, argument, result)
  , sBits :: BitsInfo
  }

-- | bitdata name ↦ (underlying integer, fields with low bit and width).
type BitsInfo = M.Map String (IntTy, [(String, Int, Int)])

data St = St
  { stNext :: Int
  , stTy :: M.Map Int Ty             -- ^ solved type variables
  , stEff :: M.Map Int (S.Set String) -- ^ effect variables: what flows into them so far
  , stUsed :: S.Set String           -- ^ names taken in the current definition
  , stBinders :: M.Map String Ty     -- ^ types of the binders of the current definition
  , stLits :: [Int]                  -- ^ type variables of width-inferred literals
  , stBits :: BitsInfo
  }

type I = StateT St (Either TypeError)

data Env = Env
  { eSig :: Sig
  , eLocals :: M.Map String (String, Ty) -- ^ source name ↦ (core name, type)
  , eRec :: S.Set String                 -- ^ recursive group of the current definition
  , eTv :: M.Map String Kind
  }

failWith :: ErrKind -> String -> I a
failWith k msg = lift (Left (TypeError k msg Nothing))

-- | Run an inference step, attaching this position to its error if it has none.
located :: Pos -> I a -> I a
located p m = StateT $ \s -> atPos p (runStateT m s)

-- | Infer a surface program; the result is a λK₃ program for "Keel.Mono".compile.
inferProgram :: Program -> Either TypeError Program
inferProgram (Program userDecls main) = evalStateT go (St 0 M.empty M.empty S.empty M.empty [] bitsInfo)
  where
    decls = optionDecl : arrayDecl : userDecls
    bitsInfo = M.fromList [(b, (it, fs)) | Bitdata b it fs <- userDecls]
    sig =
      Sig
        { sData = M.fromList [(d, (lin, ps, cs)) | Data lin d ps cs <- decls]
        , sCons = M.fromList [(c, (d, fs)) | Data _ d _ cs <- decls, (c, fs) <- cs]
        , sCodata = M.fromList [(d, (ps, os)) | Codata d ps os <- decls]
        , sDefs = M.fromList [(f, t) | Def f t _ <- userDecls]
        , sOps = M.fromList [(op, (l, a, r)) | (l, ops) <- builtinEffects ++ [(l, os) | Effect l os <- decls], (op, a, r) <- ops]
        , sBits = bitsInfo
        }
    groups = recursiveGroups userDecls
    go = do
      decls' <- forM userDecls $ \d -> case d of
        Def f t e -> do
          let (vs, _, body) = case t of
                TForall vs' es' b -> (vs', es', b)
                _ -> ([], [], t)
              env = Env sig M.empty (M.findWithDefault S.empty f groups) (M.fromList vs)
          startDef
          (e', _) <- check env e body
          Just . Def f (resolveBits bitsInfo t) <$> finish env e'
        Bitdata {} -> pure Nothing
        Data lin n ps cs -> pure (Just (Data lin n ps [(c, map (resolveBits bitsInfo) fs) | (c, fs) <- cs]))
        Codata n ps os -> pure (Just (Codata n ps [(o, resolveBits bitsInfo ot) | (o, ot) <- os]))
        Effect l ops -> pure (Just (Effect l [(op, resolveBits bitsInfo a, resolveBits bitsInfo r) | (op, a, r) <- ops]))
      startDef
      let env = Env sig M.empty S.empty M.empty
      (m, _, _) <- infer env main
      Program [d | Just d <- decls'] <$> finish env m
    startDef = modify (\s -> s {stUsed = M.keysSet (sDefs sig), stBinders = M.empty})

-- Variables ---------------------------------------------------------------------------------

freshTy :: I Ty
freshTy = do
  s <- get
  put s {stNext = stNext s + 1}
  pure (TMeta (stNext s))

freshEff :: I String
freshEff = do
  s <- get
  put s {stNext = stNext s + 1}
  pure ("?" ++ show (stNext s))

isEffMeta :: String -> Bool
isEffMeta = ("?" `isPrefixOf`)

effId :: String -> Int
effId = read . drop 1

-- | Replace holes with fresh type variables.
fill :: Ty -> I Ty
fill t = case t of
  TMeta (-1) -> freshTy
  TFun a e b -> TFun <$> fill a <*> pure e <*> fill b
  TLFun a e b -> TLFun <$> fill a <*> pure e <*> fill b
  TData d as -> TData d <$> mapM fill as
  TBox a -> TBox <$> fill a
  TPair a b -> TPair <$> fill a <*> fill b
  TRef a -> TRef <$> fill a
  TMut a -> TMut <$> fill a
  _ -> pure t

-- | Follow solved variables at the top.
shallow :: Ty -> I Ty
shallow t@(TMeta n) = do
  sol <- gets stTy
  maybe (pure t) shallow (M.lookup n sol)
shallow t = pure t

zonk :: Ty -> I Ty
zonk t = do
  t' <- shallow t
  case t' of
    TFun a e b -> TFun <$> zonk a <*> pure e <*> zonk b
    TLFun a e b -> TLFun <$> zonk a <*> pure e <*> zonk b
    TData d as -> TData d <$> mapM zonk as
    TBox a -> TBox <$> zonk a
    TPair a b -> TPair <$> zonk a <*> zonk b
    TRef a -> TRef <$> zonk a
    TMut a -> TMut <$> zonk a
    _ -> pure t'

-- | The concrete labels an effect stands for so far (effect variables expanded).
expand :: Eff -> I Eff
expand e0 = do
  sols <- gets stEff
  let go seen e = S.unions [lbl seen l | l <- S.toList e]
      lbl seen l
        | isEffMeta l, l `S.notMember` seen = go (S.insert l seen) (M.findWithDefault S.empty (effId l) sols)
        | isEffMeta l = S.empty
        | otherwise = S.singleton l
  pure (go S.empty e0)

-- | @actual ⊆ expected@: labels not already in @expected@ flow into its first effect variable.
-- With no variable to absorb them, the core checker reports the missing effect.
effLE :: Eff -> Eff -> I ()
effLE actual expected = do
  a <- expand actual
  e <- expand expected
  let extra = a S.\\ e
  case filter isEffMeta (S.toList expected) of
    v : _ | not (S.null extra) -> modify (\s -> s {stEff = M.insertWith S.union (effId v) extra (stEff s)})
    _ -> pure ()

bindMeta :: Int -> Ty -> I ()
bindMeta n t = do
  t' <- zonk t
  when (occurs t') $ failWith Mismatch ("infinite type: ?" ++ show n ++ " = " ++ prettyTy t')
  -- The type of an integer literal can only become an integer type: say so where it happens.
  lits <- gets stLits
  when (n `elem` lits) $ case t' of
    TInt _ -> pure ()
    TMeta m -> modify (\s -> s {stLits = m : stLits s})
    _ -> failWith Mismatch ("expected " ++ prettyTy t' ++ ", got an integer")
  modify (\s -> s {stTy = M.insert n t' (stTy s)})
  where
    occurs u = case u of
      TMeta m -> m == n
      TFun a _ b -> occurs a || occurs b
      TLFun a _ b -> occurs a || occurs b
      TData _ as -> any occurs as
      TBox a -> occurs a
      TPair a b -> occurs a || occurs b
      TRef a -> occurs a
      TMut a -> occurs a
      _ -> False

-- | Relate an actual type to an expected one: unification, except that with @sub@ a function
-- may have fewer effects than expected and a free function may stand for a linear one.
rel :: Bool -> Ty -> Ty -> I ()
rel sub a b = do
  a' <- shallow a
  b' <- shallow b
  case (a', b') of
    (TMeta m, TMeta n) | m == n -> pure ()
    (TMeta m, t) -> bindMeta m t
    (t, TMeta m) -> bindMeta m t
    (TFun p e r, TFun p' e' r') -> fun p e r p' e' r'
    (TFun p e r, TLFun p' e' r') | sub -> fun p e r p' e' r'
    (TLFun p e r, TLFun p' e' r') -> fun p e r p' e' r'
    (TData d as, TData d' bs) | d == d', length as == length bs -> zipWithM_ (rel False) as bs
    (TBox x, TBox y) -> rel sub x y
    (TPair x y, TPair x' y') -> rel sub x x' >> rel sub y y'
    (TRef x, TRef y) -> rel False x y
    (TMut x, TMut y) -> rel False x y
    _
      | a' == b' -> pure ()
      | otherwise -> do
          za <- zonk a'
          zb <- zonk b'
          failWith Mismatch ("expected " ++ prettyTy zb ++ ", got " ++ prettyTy za)
  where
    fun p e r p' e' r' = do
      rel sub p' p
      effLE e e'
      unless sub (effLE e' e)
      rel sub r r'

-- Binders ---------------------------------------------------------------------------------

-- | Bring a binder into scope under a name not yet taken in this definition.
binder :: Env -> String -> Ty -> I (String, Env)
binder env x t = do
  s <- get
  let x' = case dropWhile (`S.member` stUsed s) (x : [x ++ "~" ++ show i | i <- [1 :: Int ..]]) of
        n : _ -> n
        [] -> x -- unreachable: the candidates are infinite
  put s {stUsed = S.insert x' (stUsed s), stBinders = M.insert x' t (stBinders s)}
  pure (x', env {eLocals = M.insert x (x', t) (eLocals env)})

local :: Env -> String -> I (String, Ty)
local env x = maybe (failWith NotAPlace (x ++ " is not a local variable")) pure (M.lookup x (eLocals env))

-- Inference -------------------------------------------------------------------------------

check :: Env -> Term -> Ty -> I (Term, Eff)
check env (At p e) expected = located p $ do
  (e', eff) <- check env e expected
  pure (At p e', eff)
check env tm expected = do
  ex <- shallow expected
  case (tm, ex) of
    (Lam x t b, TFun p e r) -> lamAgainst Lam x t b p e r
    (Lam x t b, TLFun p e r) -> lamAgainst Lam x t b p e r
    (NumLit Nothing n, TInt _) -> pure (NumLit (Just ex) n, S.empty)
    (Con c [] args, TData d tys) | Just (d', _) <- M.lookup c (sCons sig), d == d' -> conTerm c tys args
    (Cocase d [] bs, TData d' tys) | d == d' -> cocaseTerm d tys bs
    (If c a b, _) -> do
      (c', ec) <- check env c TBool
      (a', ea) <- check env a ex
      (b', eb) <- check env b ex
      pure (If c' a' b', S.unions [ec, ea, eb])
    (Let x e b, _) -> do
      (e', te, ee) <- infer env e
      (x', env') <- binder env x te
      (b', eb) <- check env' b ex
      pure (Let x' e' b', ee <> eb)
    (Seq a b, _) -> do
      (a', ea) <- check env a TUnit
      (b', eb) <- check env b ex
      pure (Seq a' b', ea <> eb)
    (Case e alts, _) -> caseTerm e alts (Just ex)
    _ -> do
      (tm', t, eff) <- infer env tm
      rel True t ex
      pure (tm', eff)
  where
    sig = eSig env
    lamAgainst mk x t b p e r = do
      t' <- fill t
      rel False t' p
      zt <- zonk t'
      (x', env') <- binder env x (content zt)
      (b', eb) <- check env' b r
      effLE eb e
      pure (mk x' t' b', S.empty)
    conTerm c tys args = do
      (_, fields, tys') <- conInfo env c tys
      rs <- zipWithM (check env) args (map (inst env c tys') fields)
      pure (Con c tys' (map fst rs), S.unions (map snd rs))
    cocaseTerm d tys bs = do
      (ps, obs) <- codataInfo env d
      bs' <- forM bs $ \(o, b) -> do
        ot <- maybe (failWith NonExhaustive (d ++ " has no observation " ++ o)) pure (lookup o obs)
        (b', _) <- check env b (substTy (M.fromList (zip ps tys)) M.empty ot)
        pure (o, b')
      pure (Cocase d tys bs', S.empty)
    caseTerm e alts mex = do
      (_, c', eff) <- caseOf env e alts mex
      pure (c', eff)

-- | The type a binder has: a reference parameter binds its contents.
content :: Ty -> Ty
content (TMut c) = c
content (TRef c) = c
content t = t

conInfo :: Env -> String -> [Ty] -> I (String, [Ty], [Ty])
conInfo env c tys = do
  (d, fields) <- maybe (failWith Unbound ("constructor " ++ c)) pure (M.lookup c (sCons (eSig env)))
  let ps = maybe [] (\(_, p, _) -> p) (M.lookup d (sData (eSig env)))
  tys' <- if null tys then mapM (const freshTy) ps else mapM fill tys
  pure (d, fields, tys')

inst :: Env -> String -> [Ty] -> Ty -> Ty
inst env c tys =
  let d = maybe "" fst (M.lookup c (sCons (eSig env)))
      ps = maybe [] (\(_, p, _) -> p) (M.lookup d (sData (eSig env)))
   in substTy (M.fromList (zip ps tys)) M.empty

codataInfo :: Env -> String -> I ([String], [(String, Ty)])
codataInfo env d = maybe (failWith Unbound ("codata " ++ d)) pure (M.lookup d (sCodata (eSig env)))

-- | Infer a case expression; with an expected type, branches are checked against it.
caseOf :: Env -> Term -> [(String, [String], Term)] -> Maybe Ty -> I (Ty, Term, Eff)
caseOf env e alts mex = do
  (e', te, ee) <- infer env e
  (c0, _, _) <- case alts of
    a : _ -> pure a
    [] -> failWith NonExhaustive "empty case"
  (d, _, tys) <- conInfo env c0 []
  rel False te (TData d tys)
  resTy <- maybe freshTy pure mex
  -- A last alternative _ -> e stands for every constructor not listed before it: it stays one
  -- default alternative (spec/core.md §1.4), or is the alternative of the one constructor it
  -- covers (which keeps that branch's fields, for reuse).
  let cons = maybe [] (\(_, _, cs) -> cs) (M.lookup d (sData (eSig env)))
      rest' = [(c', fs) | (c', fs) <- cons, c' `notElem` [k | (k, _, _) <- alts]]
      unlisted (c, xs, b)
        | c == "_", [(c', fs)] <- rest' = [(c', map (const "_") fs, b)]
        | c == "_", null rest' = []
        | otherwise = [(c, xs, b)]
  rs <- forM (concatMap unlisted alts) $ \(c, xs, b) -> case c of
    "_" -> (\(b', eb) -> (("_", [], b'), eb)) <$> check env b resTy
    _ -> do
     (_, fields, _) <- conInfo env c []
     when (length xs /= length fields) $ failWith Mismatch (c ++ ": wrong number of pattern variables")
     (xs', env') <- binders env (zip xs (map (inst env c tys) fields))
     (b', eb) <- check env' b resTy
     pure ((c, xs', b'), eb)
  pure (resTy, Case e' (map fst rs), S.unions (ee : map snd rs))

binders :: Env -> [(String, Ty)] -> I ([String], Env)
binders env [] = pure ([], env)
binders env ((x, t) : rest) = do
  (x', env') <- binder env x t
  (xs', env'') <- binders env' rest
  pure (x' : xs', env'')

infer :: Env -> Term -> I (Term, Ty, Eff)
infer env tm = case tm of
  At p e -> located p $ do
    (e', t, eff) <- infer env e
    pure (At p e', t, eff)
  Var x
    | Just (x', t) <- M.lookup x (eLocals env) -> pure (Var x', t, S.empty)
    | Just t <- M.lookup x (sDefs sig) -> case t of
        TForall vs es body -> do
          tys <- mapM (const freshTy) vs
          effs <- mapM (const freshEff) es
          let ty = substTy (M.fromList (zip (map fst vs) tys)) (M.fromList (zip es (map S.singleton effs))) body
          pure (TyApp x tys (map S.singleton effs), ty, diverge x)
        _ -> pure (Var x, t, diverge x)
    | M.member x (sOps sig) -> failWith Mismatch ("operation " ++ x ++ " must be applied: " ++ x ++ "(…)")
    | Just AEmpty <- lookup x arrayOps -> do
        elemTy <- freshTy
        pure (ArrayPrim AEmpty elemTy [], TData "Array" [elemTy], S.empty)
    | Just op <- lookup x arrayOps -> arrayArity op >>= \n -> failWith Mismatch (x ++ " must be applied to its " ++ show n ++ " arguments (std.array has it as a function)")
    | otherwise -> failWith Unbound x
  TyApp f tys effs -> case M.lookup f (sDefs sig) of
    Just (TForall vs es body) | length tys == length vs -> do
      tys' <- mapM fill tys
      effs' <- if null effs then mapM (fmap S.singleton . const freshEff) es else pure effs
      let ty = substTy (M.fromList (zip (map fst vs) tys')) (M.fromList (zip es effs')) body
      pure (TyApp f tys' effs', ty, diverge f)
    _ -> failWith Mismatch (f ++ ": wrong type arguments")
  UnitLit -> pure (tm, TUnit, S.empty)
  BoolLit _ -> pure (tm, TBool, S.empty)
  IntLit t _ -> pure (tm, TInt t, S.empty)
  NumLit Nothing n -> do
    m <- freshTy
    case m of
      TMeta k -> modify (\s -> s {stLits = k : stLits s})
      _ -> pure ()
    pure (NumLit (Just m) n, m, S.empty)
  NumLit (Just t) _ -> pure (tm, t, S.empty)
  Convert to e -> do
    (e', te, ee) <- infer env e
    zt <- zonk te
    case zt of
      TInt _ -> pure ()
      TMeta _ -> pure () -- a literal: defaults to i64
      _ -> failWith Mismatch ("conversion of non-integer " ++ prettyTy zt)
    pure (Convert to e', TInt to, ee)
  Prim op a b -> do
    (a', ta, ea) <- infer env a
    (b', eb) <- check env b ta
    let (t, extra) = case op of
          Eq -> (TBool, S.empty)
          Lt -> (TBool, S.empty)
          Arith Checked _ -> (ta, S.singleton panicE)
          Arith Optional _ -> (TData "Option" [ta], S.empty)
          Arith _ _ -> (ta, S.empty)
          Bits _ -> (ta, S.empty)
    pure (Prim op a' b', t, S.unions [ea, eb, extra])
  If c a b -> do
    (c', ec) <- check env c TBool
    (a', ta, ea) <- infer env a
    (b', eb) <- check env b ta
    pure (If c' a' b', ta, S.unions [ec, ea, eb])
  Lam x t b -> lam Lam TFun x t b
  LLam x t b -> lam LLam TLFun x t b
  App (Var op) a
    | Nothing <- M.lookup op (eLocals env)
    , not (M.member op (sDefs sig))
    , Just (l, ta, tr) <- M.lookup op (sOps sig) -> do
        (a', ea) <- check env a ta
        pure (Perform op a', tr, S.insert l ea)
  Perform op a -> infer env (App (Var op) a)
  ArrayPrim op _ args -> infer env (foldl App (Var (concat [n | (n, o) <- arrayOps, o == op])) args)
  -- arena f is typed as f (); Lower checks that nothing allocated inside can escape.
  App (Var x) f
    | Nothing <- M.lookup x (eLocals env)
    , not (M.member x (sDefs sig))
    , Just AArena <- lookup x arrayOps -> do
        (call, r, eff) <- infer env (App f UnitLit)
        case call of
          App f' _ -> pure (ArrayPrim AArena r [f'], r, eff)
          _ -> failWith Mismatch "arena takes a function of Unit: arena (\\u. e)"
  App _ _
    | (Var x, args) <- appSpine tm
    , Nothing <- M.lookup x (eLocals env)
    , not (M.member x (sDefs sig))
    , Just op <- lookup x arrayOps -> do
        elemTy <- freshTy
        let (tys, r, eff) = arrayOpType op elemTy
        when (length args /= length tys) $
          failWith Mismatch (x ++ " takes " ++ show (length tys) ++ " arguments, given " ++ show (length args))
        rs <- zipWithM (check env) args tys
        pure (ArrayPrim op elemTy (map fst rs), r, S.unions (eff : map snd rs))
  App f a -> do
    (f', tf, ef) <- infer env f
    tf' <- shallow tf
    (p, latent, r) <- case tf' of
      TFun p e r -> pure (p, e, r)
      TLFun p e r -> pure (p, e, r)
      TMeta _ -> do
        p <- freshTy
        r <- freshTy
        v <- freshEff
        rel False tf' (TFun p (S.singleton v) r)
        pure (p, S.singleton v, r)
      _ -> do
        z <- zonk tf'
        failWith Mismatch ("applying a non-function of type " ++ prettyTy z)
    (a', ea) <- case a of
      Borrow x -> borrow TRef Borrow x p
      BorrowMut x -> borrow TMut BorrowMut x p
      _ -> check env a p
    pure (App f' a', r, S.unions [ef, ea, latent])
  Let x e b -> do
    (e', te, ee) <- infer env e
    (x', env') <- binder env x te
    (b', tb, eb) <- infer env' b
    pure (Let x' e' b', tb, ee <> eb)
  LetVar x e b -> do
    (e', te, ee) <- infer env e
    (x', env') <- binder env x te
    (b', tb, eb) <- infer env' b
    pure (LetVar x' e' b', tb, ee <> eb)
  Assign x e -> do
    (x', t) <- local env x
    (e', ee) <- check env e t
    pure (Assign x' e', TUnit, ee)
  Seq a b -> do
    (a', ea) <- check env a TUnit
    (b', tb, eb) <- infer env b
    pure (Seq a' b', tb, ea <> eb)
  -- Status(x): a bitdata value from its raw integer.
  Con c [] [x] | Just (it, _) <- M.lookup c (sBits sig) -> do
    (x', ex) <- check env x (TInt it)
    pure (x', TData c [], ex)
  BitsLit b fs -> case M.lookup b (sBits sig) of
    Nothing -> failWith Unbound ("bitdata " ++ b)
    Just (it, fields) -> do
      parts <- forM fs $ \(f, e) -> case [(lo, w) | (f', lo, w) <- fields, f' == f] of
        (lo, w) : _ -> do
          (e', ee) <- check env e (TInt it)
          pure (Prim (Bits Shl) (Prim (Bits And) e' (IntLit it (mask w))) (IntLit it (toInteger lo)), ee)
        [] -> failWith Unbound (b ++ " has no field " ++ f)
      pure (foldl (Prim (Bits Or)) (IntLit it 0) (map fst parts), TData b [], S.unions (map snd parts))
  Con c tys args -> do
    (d, fields, tys') <- conInfo env c tys
    rs <- zipWithM (check env) args (map (inst env c tys') fields)
    pure (Con c tys' (map fst rs), TData d tys', S.unions (map snd rs))
  Case e alts -> do
    (t, c', eff) <- caseOf env e alts Nothing
    pure (c', t, eff)
  Box e -> do
    (e', t, eff) <- infer env e
    pure (Box e', TBox t, eff)
  Unbox e -> do
    (e', t, eff) <- infer env e
    m <- freshTy
    rel False t (TBox m)
    pure (Unbox e', m, eff)
  Pair a b -> do
    (a', ta, ea) <- infer env a
    (b', tb, eb) <- infer env b
    pure (Pair a' b', TPair ta tb, ea <> eb)
  LetPair x y e b -> do
    (e', te, ee) <- infer env e
    m1 <- freshTy
    m2 <- freshTy
    rel False te (TPair m1 m2)
    (x', env1) <- binder env x m1
    (y', env') <- binder env1 y m2
    (b', tb, eb) <- infer env' b
    pure (LetPair x' y' e' b', tb, ee <> eb)
  Handle l body cs -> do
    (b', tb, eb) <- infer env body
    cs' <- forM cs $ \(op, x, e) -> do
      (_, ta, tr) <- maybe (failWith Unbound ("operation " ++ op)) pure (M.lookup op (sOps sig))
      (x', env') <- binder env x ta
      (e', ee) <- check env' e tr
      pure ((op, x', e'), ee)
    eb' <- expand eb
    pure (Handle l b' (map fst cs'), tb, S.unions (S.delete l eb' : map snd cs'))
  Cocase d tys bs -> do
    (ps, _) <- codataInfo env d
    tys' <- if null tys then mapM (const freshTy) ps else mapM fill tys
    (tm', _) <- check env (Cocase d [] bs) (TData d tys')
    pure (tm', TData d tys', S.empty)
  Proj e o -> do
    (e', te, ee) <- infer env e
    zt <- zonk te
    case zt of
      TData b []
        | Just (it, fields) <- M.lookup b (sBits sig) -> case [(lo, w) | (f, lo, w) <- fields, f == o] of
            _ | o == "raw" -> pure (e', TInt it, ee)
            (lo, w) : _ -> pure (Prim (Bits And) (Prim (Bits Shr) e' (IntLit it (toInteger lo))) (IntLit it (mask w)), TInt it, ee)
            [] -> failWith Unbound (b ++ " has no field " ++ o)
      TData d tys
        | Just (ps, obs) <- M.lookup d (sCodata sig)
        , Just t <- lookup o obs ->
            pure (Proj e' o, substTy (M.fromList (zip ps tys)) M.empty t, ee)
      _ -> failWith Mismatch ("can't tell the type before ." ++ o ++ " (got " ++ prettyTy zt ++ "); add a type annotation")
  Borrow x -> do
    (x', t) <- local env x
    pure (Borrow x', t, S.empty) -- outside an argument: rejected later (RefEscape)
  BorrowMut x -> do
    (x', t) <- local env x
    pure (BorrowMut x', t, S.empty)
  where
    sig = eSig env
    diverge x = if x `S.member` eRec env then S.singleton divergeE else S.empty

    lam mk arrow x t b = do
      t' <- fill t
      (x', env') <- binder env x (content t')
      (b', tb, eb) <- infer env' b
      pure (mk x' t' b', arrow t' eb tb, S.empty)

    -- A borrow argument: the parameter must be a reference to the variable's type.
    borrow refTy ctor x p = do
      (x', t) <- local env x
      rel False p (refTy t)
      pure (ctor x', S.empty)

-- Finishing -------------------------------------------------------------------------------

-- | Replace solved variables, default the rest (literals to i64, other types to Unit,
-- effects to nothing), and choose λ or λ° by what each λ captures.
finish :: Env -> Term -> I Term
finish env tm = do
  -- Literals nothing constrained are i64, along with everything unified with them.
  lits <- gets stLits
  forM_ lits $ \k -> do
    z <- shallow (TMeta k)
    case z of
      TMeta k' -> bindMeta k' (TInt i64)
      _ -> pure ()
  tm' <- zonkTerm tm
  bs <- gets stBinders
  bs' <- traverse finalTy bs
  pure (linearize env bs' tm')

finalTy :: Ty -> I Ty
finalTy t = do
  z <- zonk t
  bits <- gets stBits
  resolveBits bits <$> deflt z
  where
    deflt u = case u of
      TMeta _ -> pure TUnit
      TFun a e b -> TFun <$> deflt a <*> finalEff e <*> deflt b
      TLFun a e b -> TLFun <$> deflt a <*> finalEff e <*> deflt b
      TData d as -> TData d <$> mapM deflt as
      TBox a -> TBox <$> deflt a
      TPair a b -> TPair <$> deflt a <*> deflt b
      TRef a -> TRef <$> deflt a
      TMut a -> TMut <$> deflt a
      _ -> pure u

finalEff :: Eff -> I Eff
finalEff e = do
  e' <- expand e
  pure (S.filter (not . isEffMeta) (e' <> S.filter (not . isEffMeta) e))

zonkTerm :: Term -> I Term
zonkTerm tm = do
  here <- case tm of
    Lam x t b -> (\t' -> Lam x t' b) <$> finalTy t
    LLam x t b -> (\t' -> LLam x t' b) <$> finalTy t
    Con c tys as -> (\tys' -> Con c tys' as) <$> mapM finalTy tys
    ArrayPrim op t as -> (\t' -> ArrayPrim op t' as) <$> finalTy t
    TyApp f tys effs -> TyApp f <$> mapM finalTy tys <*> mapM finalEff effs
    Cocase d tys bs -> (\tys' -> Cocase d tys' bs) <$> mapM finalTy tys
    NumLit (Just t) n -> do
      z <- zonk t
      case z of
        TInt it -> pure (IntLit it n)
        TMeta _ -> pure (IntLit i64 n)
        _ -> failWith Mismatch ("integer literal " ++ show n ++ " used as " ++ prettyTy z)
    NumLit Nothing n -> pure (IntLit i64 n)
    _ -> pure tm
  descendM zonkTerm here

-- | A field of @w@ bits, as a mask.
mask :: Int -> Integer
mask w = 2 ^ w - 1

-- | bitdata types are their underlying integers in the output.
resolveBits :: BitsInfo -> Ty -> Ty
resolveBits bits t = case t of
  TData b [] | Just (it, _) <- M.lookup b bits -> TInt it
  TFun a e r -> TFun (go a) e (go r)
  TLFun a e r -> TLFun (go a) e (go r)
  TData d as -> TData d (map go as)
  TBox a -> TBox (go a)
  TPair a b -> TPair (go a) (go b)
  TRef a -> TRef (go a)
  TMut a -> TMut (go a)
  TForall vs es b -> TForall vs es (go b)
  _ -> t
  where
    go = resolveBits bits

-- | λ captures a linear value ⇒ λ°.
linearize :: Env -> M.Map String Ty -> Term -> Term
linearize env bs = go
  where
    go tm = case descend go tm of
      Lam x t b | capturesLin x b -> LLam x t b
      t -> t
    capturesLin x b = any linVar (S.toList (S.delete x (freeVars b)))
    linVar v = maybe False ((== Lin) . kindOf) (M.lookup v bs)
    kindOf t = case t of
      TLFun {} -> Lin
      TBox a -> kindOf a
      TPair a b | Lin `elem` [kindOf a, kindOf b] -> Lin
      TVar a -> M.findWithDefault Lin a (eTv env)
      TData d as
        | Just (lin, _, _) <- M.lookup d (sData (eSig env)), lin || any ((== Lin) . kindOf) as -> Lin
      _ -> Free

-- | The head of an application and its arguments in order.
appSpine :: Term -> (Term, [Term])
appSpine (App f a) = let (h, as) = appSpine f in (h, as ++ [a])
appSpine t = (t, [])

arrayArity :: ArrayOp -> I Int
arrayArity op = (\(ts, _, _) -> length ts) . arrayOpType op <$> freshTy

freeVars :: Term -> S.Set String
freeVars tm = case tm of
  Var x -> S.singleton x
  Lam x _ b -> S.delete x (freeVars b)
  LLam x _ b -> S.delete x (freeVars b)
  Let x e b -> freeVars e <> S.delete x (freeVars b)
  LetVar x e b -> freeVars e <> S.delete x (freeVars b)
  LetPair x y e b -> freeVars e <> (freeVars b S.\\ S.fromList [x, y])
  Case e alts -> freeVars e <> S.unions [freeVars b S.\\ S.fromList xs | (_, xs, b) <- alts]
  Handle _ e cs -> freeVars e <> S.unions [S.delete x (freeVars b) | (_, x, b) <- cs]
  Assign x e -> S.insert x (freeVars e)
  Borrow x -> S.singleton x
  BorrowMut x -> S.singleton x
  _ -> S.unions (map freeVars (children tm))
