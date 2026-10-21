-- | Optimizations on monomorphic Keel Core (M4, spec/perf.md). They make "explicit dictionaries
-- + monomorphization" free (notes.md §4, §16):
--
-- 1. __Specialization on constants.__ A call @f … c …@ where @c@ is a top-level cocase (a
--    dictionary or interface implementation) or a top-level function uses a copy of @f@ with
--    that parameter replaced by @c@. Recursive calls pass @c@ along, so they reach the same
--    copy. Closed λ arguments (@map (\x. x + 1) xs@) are first lifted to top-level definitions,
--    so they specialize too, and the inliner then removes the call through the closure.
-- 2. __Inlining.__ @c.o@ on a known cocase becomes the branch; calls to small non-recursive
--    definitions are replaced by their bodies.
-- 3. __β-reduction.__ @(λx. b) a@ becomes @let x = a in b@, and a @let@ in function position
--    floats out; both keep call-by-value evaluation order.
-- 4. __Dead definitions__ (not reachable from @main@) are removed.
--
-- Inlined code is renamed apart, since the core forbids shadowing. The result is checked
-- again by the core checker ("Keel.Mono".compile).
module Keel.Opt (optimize) where

import Control.Monad (forM)
import Control.Monad.Trans.State.Strict (State, evalState, get, gets, modify, put, runState)
import Data.List (intercalate)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Check (recursiveGroups, typeOfClosed)
import Keel.Syntax

optimize :: Program -> Program
optimize = removeDead . simplify . specialize . liftClosed

-- Lifting closed λ arguments ------------------------------------------------------------------

-- | Give every closed λ passed to a top-level function its own top-level definition. A λ whose
-- type can't be computed (which can't happen for checked programs) is left in place.
liftClosed :: Program -> Program
liftClosed (Program decls main) = Program (decls' ++ [Def f t e | (f, t, e) <- reverse lifted]) main'
  where
    globals = S.fromList [f | Def f _ _ <- decls]
    ((decls', main'), (_, lifted)) = runState ((,) <$> mapM liftDecl decls <*> go main) (0 :: Int, [])
    liftDecl d = case d of
      Def f t e -> Def f t <$> go e
      _ -> pure d
    go tm = case spine tm of
      (Var f, args@(_ : _)) | f `S.member` globals -> foldl App (Var f) <$> mapM liftArg args
      _ -> descendM go tm
    liftArg a = do
      a' <- go a
      case a' of
        _ | isLam a', S.null (freeVars a' S.\\ globals), Right t <- typeOfClosed decls a' -> do
          (n, acc) <- get
          let name = "lam'" ++ show n
          put (n + 1, (name, t, a') : acc)
          pure (Var name)
        _ -> pure a'
    isLam Lam {} = True
    isLam LLam {} = True
    isLam _ = False

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

-- | Worklist state: definitions so far, and specializations made (key ↦ new name).
data SS = SS {ssDefs :: M.Map String (Ty, Term), ssMade :: M.Map String String, ssTodo :: [String]}

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
    (main', order) = evalState run (SS original M.empty (M.keys original))
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

    -- The specialized copy for these arguments, if any are constants (and not all of them).
    specFor f args = do
      defs <- gets ssDefs
      case M.lookup f defs of
        Nothing -> pure Nothing
        Just (t, e) -> do
          let (ps, _) = params e
              n = min (length ps) (length args)
              fixed = [(i, g) | (i, Var g) <- zip [0 .. n - 1] args, g `S.member` consts]
          if null fixed || length fixed == length ps
            then pure Nothing
            else do
              let key = f ++ "{" ++ intercalate "," [show i ++ "=" ++ g | (i, g) <- fixed] ++ "}"
                  kept = [a | (i, a) <- zip [0 ..] args, i `notElem` map fst fixed]
              made <- gets ssMade
              case M.lookup key made of
                Just name -> pure (Just (name, kept))
                Nothing -> do
                  modify (\st -> st {ssMade = M.insert key key made})
                  let (ps', body) = params e
                      subst = M.fromList [(x, Var g) | (i, g) <- fixed, let (x, _, _) = ps' !! i]
                      keepPs = [p | (i, p) <- zip [0 ..] ps', i `notElem` map fst fixed]
                      body' = foldr (\(x, ty, lin) b -> (if lin then LLam else Lam) x ty b) (replaceVars subst body) keepPs
                      (arrs, res) = arrows (length ps') t
                      eff = S.unions [ef | (_, ef, _) <- arrs]
                      keptArrs = [a | (i, a) <- zip [0 ..] arrs, i `notElem` map fst fixed]
                      t' = rebuild keptArrs eff res
                  modify (\st -> st {ssDefs = M.insert key (t', body') (ssDefs st), ssTodo = key : ssTodo st})
                  pure (Just (key, kept))

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
        -- calls to small definitions
        App (Var f) a | Just e <- M.lookup f inlinable -> do
          e' <- rename e
          beta e' a
        App f a -> beta f a
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
size = length . universe

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
