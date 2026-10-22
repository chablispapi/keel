-- | Optimizations on monomorphic Keel Core (M4, spec/perf.md). They make "explicit dictionaries
-- + monomorphization" free (notes.md §4, §16):
--
-- 1. __Specialization on constants.__ A call @f … c …@ where @c@ is a top-level cocase (a
--    dictionary or interface implementation) or a top-level function uses a copy of @f@ with
--    that parameter replaced by @c@. Recursive calls pass @c@ along, so they reach the same
--    copy. Closed λ arguments (@map (\x. x + 1) xs@) are first lifted to top-level definitions,
--    so they specialize too, and the inliner then removes the call through the closure. A λ
--    capturing locals is lifted with them as extra parameters, and the copy takes them instead.
-- 2. __Inlining.__ @c.o@ on a known cocase becomes the branch; calls to small non-recursive
--    definitions are replaced by their bodies, and constant definitions (@def none = None@,
--    @array.empty@) by their values, so no top-level value outlives optimization.
-- 3. __β-reduction.__ @(λx. b) a@ becomes @let x = a in b@, and a @let@ in function position
--    floats out; both keep call-by-value evaluation order. Likewise a pair or constructor taken
--    apart where it is built (@let (x, y) = (a, b) in e@, @case C(a) of { C(x) -> e | … }@)
--    becomes @let@s of its components: no block is allocated.
-- 4. __Dead definitions__ (not reachable from @main@) are removed.
--
-- Inlined code is renamed apart, since the core forbids shadowing. The result is checked
-- again by the core checker ("Keel.Mono".compile).
module Keel.Opt (optimize, optimizeWith) where

import Control.Monad (forM)
import Control.Monad.Trans.State.Strict (State, evalState, get, gets, modify, put, runState)
import Data.List (intercalate)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Check (localTypes, recursiveGroups, typeOfClosed)
import Keel.Syntax

optimize :: Program -> Program
optimize = optimizeWith False

-- | With @debug@, positions stay on computations (calls, arithmetic, case, …) for the line
-- table (@keelc build -g@); otherwise they are stripped.
optimizeWith :: Bool -> Program -> Program
optimizeWith debug = removeDead . simplify . specialize . liftClosed . positions
  where
    positions = if debug then thinPositions else stripPositions

stripPositions :: Program -> Program
stripPositions (Program decls main) = Program [strip d | d <- decls] (stripAt main)
  where
    strip (Def f t e) = Def f t (stripAt e)
    strip d = d

-- | Keep positions only on computations. The rewrites below match λs, lets, variables and
-- cocases directly under applications and projections, so those must not sit under a position.
thinPositions :: Program -> Program
thinPositions (Program decls main) = Program [thinDecl d | d <- decls] (thin main)
  where
    thinDecl (Def f t e) = Def f t (thin e)
    thinDecl d = d
    thin tm = case tm of
      At p e -> let e' = thin e in if computation e' then At p e' else e'
      _ -> descend thin tm
    computation e = case e of
      App {} -> True
      Prim {} -> True
      Perform {} -> True
      ArrayPrim {} -> True
      Case {} -> True
      If {} -> True
      Proj {} -> True
      Handle {} -> True
      Convert {} -> True
      Con _ _ (_ : _) -> True
      _ -> False

-- Lifting closed λ arguments ------------------------------------------------------------------

-- | Give every closed λ passed to a top-level function its own top-level definition. A λ
-- capturing locals @y z@ becomes @lam'n y z@ for @lam'n = λy z. λ…@, a partial application of
-- a known function that specialization then takes apart; only when the parameter it is passed
-- for is only called (see 'onlyCalled'), else the copy would build a closure at each use. A λ
-- whose type can't be computed (which can't happen for checked programs) is left in place.
liftClosed :: Program -> Program
liftClosed (Program decls main) = Program (decls' ++ [Def f t e | (f, t, e) <- reverse lifted]) main'
  where
    globals = S.fromList [f | Def f _ _ <- decls]
    bodies = M.fromList [(f, e) | Def f _ e <- decls]
    ((decls', main'), (_, lifted)) = runState ((,) <$> mapM liftDecl decls <*> liftIn main) (0 :: Int, [])
    liftDecl d = case d of
      Def f t e -> Def f t <$> liftIn e
      _ -> pure d
    liftIn e = go (localTypes decls e) e
    go tys tm = case spine tm of
      -- The elaborator names the function before effectful arguments (let a = f in a …).
      _ | Let x (Var g) b <- tm, g `S.member` globals -> go tys (replaceVars (M.singleton x (Var g)) b)
      (Var f, args@(_ : _)) | f `S.member` globals -> foldl App (Var f) <$> mapM (uncurry (liftArg tys f)) (zip [0 ..] args)
      _ -> descendM (go tys) tm
    liftArg tys f i a = do
      a' <- go tys a
      let captured = S.toList (freeVars a' S.\\ globals)
          lifts
            | null captured = isLam a'
            | Lam {} <- a', Just (ps, body) <- params <$> M.lookup f bodies, i < length ps =
                let (x, _, _) = ps !! i in onlyCalled f i x body
            | otherwise = False
      case mapM (`M.lookup` tys) captured of
        Just cts
          | lifts
          , Right t <- typeOfClosed decls (foldr (uncurry Lam) a' (zip captured cts)) -> do
              (n, acc) <- get
              let name = "lam'" ++ show n
              put (n + 1, (name, t, foldr (uncurry Lam) a' (zip captured cts)) : acc)
              pure (foldl App (Var name) (map Var captured))
        _ -> pure a'
    isLam Lam {} = True
    isLam LLam {} = True
    isLam _ = False

-- | Every occurrence of @x@ in @body@ is called, or passed along as argument @i@ of @f@: then
-- replacing @x@ by a partial application builds no closure.
onlyCalled :: String -> Int -> String -> Term -> Bool
onlyCalled f i x = go
  where
    go tm = case spine tm of
      (Var h, args@(_ : _))
        | h == x -> all go args
        | h == f -> and [if stripAt a == Var x then j == i else go a | (j, a) <- zip [0 :: Int ..] args]
      _ -> case tm of
        Var y -> y /= x
        _ -> all go (children tm)

freeVars :: Term -> S.Set String
freeVars tm = case tm of
  Var x -> S.singleton x
  Lam x _ b -> S.delete x (freeVars b)
  LLam x _ b -> S.delete x (freeVars b)
  Let x e b -> freeVars e <> S.delete x (freeVars b)
  LetPair x y e b -> freeVars e <> (freeVars b S.\\ S.fromList [x, y])
  Case e alts -> freeVars e <> S.unions [freeVars b S.\\ S.fromList xs | (_, xs, b) <- alts]
  Handle _ e cs -> freeVars e <> S.unions [S.delete x (freeVars b) | (_, x, b) <- cs]
  _ -> S.unions (map freeVars (children tm))

-- Specialization -----------------------------------------------------------------------------

-- | Leading λ parameters of a definition: (name, type, linear λ?) and the body.
params :: Term -> ([(String, Ty, Bool)], Term)
params (Lam x t b) = let (ps, body) = params b in ((x, t, False) : ps, body)
params (LLam x t b) = let (ps, body) = params b in ((x, t, True) : ps, body)
params t = ([], t)

spine :: Term -> (Term, [Term])
spine (App f a) = let (h, as) = spine f in (h, as ++ [a])
spine t = (t, [])

-- | Arrow components of a definition's type, outermost first: (parameter, effect, linear?),
-- and the final result.
arrows :: Int -> Ty -> ([(Ty, Eff, Bool)], Ty)
arrows 0 t = ([], t)
arrows n (TFun a e r) = let (as, res) = arrows (n - 1) r in ((a, e, False) : as, res)
arrows n (TLFun a e r) = let (as, res) = arrows (n - 1) r in ((a, e, True) : as, res)
arrows _ t = ([], t)

-- | Worklist state: definitions so far, specializations made (key ↦ new name), and each
-- definition's body before its calls were rewritten (for 'onlyCalled').
data SS = SS {ssDefs :: M.Map String (Ty, Term), ssMade :: M.Map String String, ssTodo :: [String], ssRaw :: M.Map String Term}

specialize :: Program -> Program
specialize (Program decls main) = Program (others ++ [Def f t e | (f, (t, e)) <- order]) main'
  where
    others = [d | d <- decls, not (isDef d)]
    isDef Def {} = True
    isDef _ = False
    -- Constants: dictionaries (cocases) and top-level functions.
    consts = S.fromList [g | Def g _ e <- decls, isConst e]
    isConst e = case e of
      Cocase {} -> True
      Lam {} -> True
      LLam {} -> True
      _ -> False
    original = M.fromList [(f, (t, e)) | Def f t e <- decls]
    (main', order) = evalState run (SS original M.empty (M.keys original) (M.map snd original))
    run = do
      m <- rewrite main
      loop
      final <- gets ssDefs
      pure (m, M.toList final)
    loop = do
      s <- get
      case ssTodo s of
        [] -> pure ()
        f : rest -> do
          put s {ssTodo = rest}
          case M.lookup f (ssDefs s) of
            Just (t, e) -> do
              e' <- rewrite e
              modify (\st -> st {ssDefs = M.insert f (t, e') (ssDefs st)})
            Nothing -> pure ()
          loop

    -- Replace calls with constant arguments by calls to specialized copies.
    rewrite :: Term -> State SS Term
    rewrite tm = case spine tm of
      (Var f, args@(_ : _)) | M.member f original -> do
        args' <- mapM rewrite args
        target <- specFor f args'
        pure $ case target of
          Just (g, kept) -> foldl App (Var g) kept
          Nothing -> foldl App (Var f) args'
      _ -> descendM rewrite tm

    -- The specialized copy for these arguments, if any are constants (and not all of them). A
    -- constant is a top-level cocase or function, or a function partially applied to
    -- variables (a lifted capturing λ): the copy takes those variables as parameters instead.
    specFor f args = do
      defs <- gets ssDefs
      raw <- gets ssRaw
      case M.lookup f defs of
        Nothing -> pure Nothing
        Just (t, e) -> do
          let (ps, _) = params e
              n = min (length ps) (length args)
              (_, rawBody) = params (M.findWithDefault e f raw)
              known i a = case spine a of
                (Var g, []) | g `S.member` consts -> Just (g, [])
                (Var g, cs@(_ : _))
                  | g `S.member` consts
                  , Just vs <- mapM var cs
                  , Just (gt, ge) <- M.lookup g defs
                  , length vs < length (fst (params ge))
                  , let (x, _, _) = ps !! i
                  , onlyCalled f i x rawBody ->
                      Just (g, [(v, ty, lin) | (v, (ty, _, lin)) <- zip vs (fst (arrows (length vs) gt))])
                _ -> Nothing
              fixed = [(i, k) | (i, a) <- zip [0 .. n - 1] args, Just k <- [known i a]]
          if null fixed || (length fixed == length ps && all (null . snd . snd) fixed)
            then pure Nothing
            else do
              let key = f ++ "{" ++ intercalate "," [show i ++ "=" ++ g ++ (if null cs then "" else "/" ++ show (length cs)) | (i, (g, cs)) <- fixed] ++ "}"
                  kept = concat [maybe [a] (map (\(v, _, _) -> Var v) . snd) (lookup i fixed) | (i, a) <- zip [0 ..] args]
              made <- gets ssMade
              case M.lookup key made of
                Just name -> pure (Just (name, kept))
                Nothing -> do
                  modify (\st -> st {ssMade = M.insert key key made})
                  let (ps', body) = params e
                      -- The captured variables become fresh parameters (simplify's fresh
                      -- names are digits after the quote, so these can't collide).
                      captured i = case lookup i fixed of
                        Just (_, cs) -> let (x, _, _) = ps' !! i in [(x ++ "'c" ++ show j, ty, lin) | (j, (_, ty, lin)) <- zip [0 :: Int ..] cs]
                        Nothing -> []
                      subst = M.fromList [(x, foldl App (Var g) [Var c | (c, _, _) <- captured i]) | (i, (g, _)) <- fixed, let (x, _, _) = ps' !! i]
                      newPs = concat [maybe [p] (const (captured i)) (lookup i fixed) | (i, p) <- zip [0 ..] ps']
                      body' = foldr (\(x, ty, lin) b -> (if lin then LLam else Lam) x ty b) (replaceVars subst body) newPs
                      (arrs, res) = arrows (length ps') t
                      eff = S.unions [ef | (_, ef, _) <- arrs]
                      newArrs = concat [maybe [a] (const [(ty, S.empty, lin) | (_, ty, lin) <- captured i]) (lookup i fixed) | (i, a) <- zip [0 ..] arrs]
                      t' = rebuild newArrs eff res
                  modify (\st -> st {ssDefs = M.insert key (t', body') (ssDefs st), ssTodo = key : ssTodo st, ssRaw = M.insert key body' (ssRaw st)})
                  pure (Just (key, kept))
    var a = case stripAt a of
      Var v -> Just v
      _ -> Nothing

    -- Intermediate arrows of nested λs are pure; the last carries every effect.
    rebuild [] _ res = res
    rebuild [(a, _, lin)] eff res = (if lin then TLFun else TFun) a eff res
    rebuild ((a, _, lin) : rest) eff res = (if lin then TLFun else TFun) a S.empty (rebuild rest eff res)

-- | Replace free occurrences of variables (binders are unique, so no capture).
replaceVars :: M.Map String Term -> Term -> Term
replaceVars s (Var x) = fromMaybe (Var x) (M.lookup x s)
replaceVars s tm = descend (replaceVars s) tm

-- Simplification ------------------------------------------------------------------------------

-- | Inline, β-reduce and float lets, a few rounds.
simplify :: Program -> Program
simplify (Program decls main) = evalState go (0 :: Int)
  where
    defs = M.fromList [(f, e) | Def f _ e <- decls]
    consts = M.fromList [(g, bs) | Def g _ (Cocase _ _ bs) <- decls]
    groups = recursiveGroups decls
    recursive f = f `S.member` M.findWithDefault S.empty f groups
    -- Small, non-recursive λ definitions are inlined at calls.
    inlinable =
      M.fromList
        [ (f, e)
        | (f, e) <- M.toList defs
        , isLam e
        , not (recursive f)
        , size e <= 24
        ]
    isLam Lam {} = True
    isLam LLam {} = True
    isLam _ = False
    constants = M.fromList [(f, e') | (f, e) <- M.toList defs, let e' = stripAt e, constant e']
    constant e = case e of
      UnitLit -> True
      BoolLit _ -> True
      IntLit _ _ -> True
      Con _ _ [] -> True
      ArrayPrim AEmpty _ [] -> True
      _ -> False

    go = do
      decls' <- forM decls $ \d -> case d of
        Def f t e -> Def f t <$> rounds 4 e
        _ -> pure d
      Program decls' <$> rounds 4 main

    rounds :: Int -> Term -> State Int Term
    rounds 0 e = pure e
    rounds k e = do
      e' <- simp e
      if e' == e then pure e else rounds (k - 1) e'

    simp :: Term -> State Int Term
    simp tm = do
      tm' <- descendM simp tm
      case tm' of
        -- c.o on a known cocase: the branch (renamed apart)
        Proj (Var g) o | Just bs <- M.lookup g consts, Just b <- lookup o bs -> rename b
        Var g | Just e <- M.lookup g constants -> pure e
        -- calls to small definitions
        App (Var f) a | Just e <- M.lookup f inlinable -> do
          e' <- rename e
          beta e' a
        App f a -> beta f a
        -- A pair or constructor taken apart where it is built: no block, its components bound
        -- in order (the core forbids shadowing, so no component sees the new names).
        LetPair x y e b | Pair p q <- stripAt e -> pure (Let x p (Let y q b))
        Case e alts | Con c _ args <- stripAt e, Just (xs, b) <- lookup c [(c', (xs, b)) | (c', xs, b) <- alts] -> pure (foldr (uncurry Let) b (zip xs args))
        _ -> pure tm'

    -- (λx. b) a ⇒ let x = a in b;  (let x = e in b) a ⇒ let x' = e in (b a). The floated
    -- binder is renamed: @a@ now sits in its scope and may bind the same name.
    beta f a = case f of
      Lam x _ b -> pure (Let x a b)
      LLam x _ b -> pure (Let x a b)
      Let x e b -> do
        x' <- freshName x
        Let x' e <$> beta (replaceVars (M.singleton x (Var x')) b) a
      _ -> pure (App f a)

-- | A fresh variant of a name (source names never contain @'@).
freshName :: String -> State Int String
freshName x = do
  n <- get
  put (n + 1)
  pure (takeWhile (/= '\'') x ++ "'" ++ show n)

-- | Rename every binder in a term to a fresh name.
rename :: Term -> State Int Term
rename = go M.empty
  where
    fresh = freshName
    go env tm = case tm of
      Var x -> pure (Var (M.findWithDefault x x env))
      Lam x t b -> bind1 x $ \x' env' -> Lam x' t <$> go env' b
      LLam x t b -> bind1 x $ \x' env' -> LLam x' t <$> go env' b
      Let x e b -> do
        e' <- go env e
        bind1 x $ \x' env' -> Let x' e' <$> go env' b
      LetPair x y e b -> do
        e' <- go env e
        x' <- fresh x
        y' <- fresh y
        LetPair x' y' e' <$> go (M.insert x x' (M.insert y y' env)) b
      Case e alts -> do
        e' <- go env e
        alts' <- forM alts $ \(c, xs, b) -> do
          xs' <- mapM fresh xs
          (c,xs',) <$> go (M.union (M.fromList (zip xs xs')) env) b
        pure (Case e' alts')
      Handle l e cs -> do
        e' <- go env e
        cs' <- forM cs $ \(op, x, b) -> do
          x' <- fresh x
          (op,x',) <$> go (M.insert x x' env) b
        pure (Handle l e' cs')
      _ -> descendM (go env) tm
      where
        bind1 x k = do
          x' <- fresh x
          k x' (M.insert x x' env)

size :: Term -> Int
size tm = length [() | t <- universe tm, not (isAt t)]
  where
    isAt At {} = True
    isAt _ = False

-- Dead definitions -----------------------------------------------------------------------------

removeDead :: Program -> Program
removeDead (Program decls main) = Program [d | d <- decls, keep d] main
  where
    defs = M.fromList [(f, e) | Def f _ e <- decls]
    refs e = [x | Var x <- universe e, M.member x defs]
    live = go S.empty (refs main)
    go seen [] = seen
    go seen (f : fs)
      | f `S.member` seen = go seen fs
      | otherwise = go (S.insert f seen) (maybe [] refs (M.lookup f defs) ++ fs)
    keep (Def f _ _) = f `S.member` live
    keep _ = True
