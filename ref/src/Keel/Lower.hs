-- | Lowering (notes.md §5, §17): monomorphic Keel Core → A-normal form → closure conversion →
-- a first-order IR that maps one-to-one onto assembly.
--
-- Covered (M1): all integer widths, Bool, Unit, arithmetic in every overflow mode, if, let,
-- λ / λ°, application, recursive top-level definitions, data and case, Box, pairs, codata,
-- and the built-in @out@. Effect handlers come with M3 and are reported as unsupported.
--
-- Representation: every value is one 64-bit word. Integers are sign- or zero-extended to
-- 64 bits by their type; Bool and Unit are 0/1 and 0. Data values, pairs, closures and codata
-- values are pointers to heap blocks: @[tag, fields…]@, @[code, captured…]@ and
-- @[code₁, …, codeₙ, captured…]@. @Box@ is the identity, since data is already behind a pointer.
module Keel.Lower (Atom (..), Rhs (..), Expr (..), Fun (..), LProg (..), lower) where

import Control.Applicative ((<|>))
import Control.Monad (forM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, put, runStateT)
import Data.List (elemIndex, sortOn)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Syntax

data Atom
  = AInt Integer -- ^ integers (canonical 64-bit form), and Bool / Unit as 0 or 1
  | AVar String  -- ^ a local variable (stack slot)
  | AGlobal Int  -- ^ the static closure of top-level function i
  deriving (Show)

data Rhs
  = RAtom Atom
  | RPrim Prim IntTy Atom Atom -- ^ arithmetic or comparison at an integer type
  | RCall Atom Atom           -- ^ call an unknown closure
  | RCallKnown Int Atom       -- ^ direct call to top-level function i (the video's "free" case)
  | RClosure Int [String]     -- ^ allocate a closure for function i capturing these locals
  | RCodata [Int] [String]    -- ^ allocate a codata value: one function per observation
  | RProj Atom Int            -- ^ observe: call the i-th function of a codata value
  | RAlloc Integer [Atom]     -- ^ allocate a data block with a tag and fields
  | RField Atom Int           -- ^ load field i of a data block
  | ROut Atom                 -- ^ print an integer
  deriving (Show)

data Expr
  = Ret Atom                                  -- ^ the value of this expression
  | Bind String Rhs Expr                      -- ^ let x = rhs in e
  | BindIf String Atom Expr Expr Expr         -- ^ let x = (if a then e₁ else e₂) in e
  | BindCase String Atom [(Integer, Expr)] Expr -- ^ let x = (case on the tag of a) in e
  deriving (Show)

-- | A closure-converted function, called with its block in x0 and one argument in x1. Its
-- captured values start at word @funEnvBase@ of the block.
data Fun = Fun {funName :: String, funParam :: String, funEnvBase :: Int, funEnv :: [String], funBody :: Expr}
  deriving (Show)

-- | Functions are numbered: top-level λ definitions keep their definition's index, lifted
-- functions follow. Every top-level definition i also has a static block @_kc_i@, listed in
-- @lStatics@ with the functions it points to: one for a λ (its static closure), one per
-- observation for a cocase. @main@ is a separate body.
data LProg = LProg {lFuns :: M.Map Int Fun, lStatics :: [(Int, String, [Int])], lMain :: Expr}
  deriving (Show)

-- | What lowering needs to know about declarations.
data Info = Info
  { iGlobals :: M.Map String (Int, Ty)
  , iKnown :: S.Set String                        -- ^ top-level λs: callable directly
  , iCons :: M.Map String (Integer, String, [Ty]) -- ^ constructor ↦ (tag, data name, field types)
  , iParams :: M.Map String [String]              -- ^ data / codata name ↦ parameters
  , iObs :: M.Map String [(String, Ty)]           -- ^ codata name ↦ observations in order
  , iOps :: M.Map String Ty                       -- ^ operation ↦ result type
  }

-- | Fresh-name counter and lifted functions (index ↦ function).
type M = StateT (Int, M.Map Int Fun) (Either String)

fresh :: M String
fresh = do
  (n, fs) <- get
  put (n + 1, fs)
  pure ("%t" ++ show n)

unsupported :: String -> M a
unsupported what = lift (Left ("not supported yet: " ++ what))

-- | Register a lifted function and return its index (after all definition indices).
liftFun :: Info -> Fun -> M Int
liftFun info f = do
  (n, fs) <- get
  let ng = M.size (iGlobals info)
      i = case M.lookupMax fs of
        Just (k, _) | k >= ng -> k + 1
        _ -> ng
  put (n, M.insert i f fs)
  pure i

-- | Lower a monomorphic core program (the output of "Keel.Mono".compile).
lower :: Program -> Either String LProg
lower (Program userDecls main) = do
  let decls = optionDecl : userDecls
      defs = [(f, t, e) | Def f t e <- decls]
      info =
        Info
          { iGlobals = M.fromList [(f, (i, t)) | (i, (f, t, _)) <- zip [0 ..] defs]
          , iKnown = S.fromList [f | (f, _, e) <- defs, isLam e]
          , iCons = M.fromList [(c, (tag, d, fs)) | Data _ d _ cs <- decls, (tag, (c, fs)) <- zip [0 ..] cs]
          , iParams = M.fromList ([(d, ps) | Data _ d ps _ <- decls] ++ [(d, ps) | Codata d ps _ <- decls])
          , iObs = M.fromList [(d, os) | Codata d _ os <- decls]
          , iOps = M.fromList (("out", TUnit) : [(op, r) | Effect _ ops <- decls, (op, _, r) <- ops])
          }
  ((statics, mainE), (_, funs)) <-
    runStateT
      ( do
          statics <- forM (zip [0 ..] defs) $ \(i, (f, _, e)) -> case e of
            Lam x t b -> topLam info i f x t b
            LLam x t b -> topLam info i f x t b
            -- A closed cocase is a static block of observation functions.
            Cocase d _ bs -> do
              let obs = M.findWithDefault [] d (iObs info)
              is <- forM obs $ \(o, _) -> do
                body <- expr info M.empty (fromMaybe UnitLit (lookup o bs)) (pure . Ret)
                liftFun info (Fun (f ++ "." ++ o) "%self" (length obs) [] body)
              pure (i, f, is)
            _ -> unsupported ("top-level definition " ++ f ++ " that is neither a λ nor a cocase")
          m <- expr info M.empty main (pure . Ret)
          pure (statics, m)
      )
      (0, M.empty)
  pure (LProg funs statics mainE)
  where
    isLam e = case e of
      Lam {} -> True
      LLam {} -> True
      _ -> False

-- | A top-level λ keeps its definition's index; its static block is its closure.
topLam :: Info -> Int -> String -> String -> Ty -> Term -> M (Int, String, [Int])
topLam info i f x t b = do
  body <- expr info (M.singleton x t) b (pure . Ret)
  (n, fs) <- get
  put (n, M.insert i (Fun f x 1 [] body) fs)
  pure (i, f, [i])

-- | Types of the locals in scope.
type Env = M.Map String Ty

-- | CPS-style ANF conversion: @k@ receives an atom for the value of the term.
expr :: Info -> Env -> Term -> (Atom -> M Expr) -> M Expr
expr info env tm k = case tm of
  Var x -> k (maybe (AVar x) (AGlobal . fst) (M.lookup x (iGlobals info)))
  UnitLit -> k (AInt 0)
  BoolLit b -> k (AInt (if b then 1 else 0))
  IntLit _ n -> k (AInt n)
  Prim op a b -> case typeOf info env a of
    TInt it -> sub a $ \va -> sub b $ \vb -> bindRhs (RPrim op it va vb)
    t -> lift (Left ("arithmetic on " ++ prettyTy t))
  Let x e b -> sub e $ \v -> Bind x (RAtom v) <$> expr info (M.insert x (typeOf info env e) env) b k
  If c a b -> sub c $ \vc -> do
    x <- fresh
    ea <- branch env a
    eb <- branch env b
    BindIf x vc ea eb <$> k (AVar x)
  Lam x t b -> closure x t b
  LLam x t b -> closure x t b
  App (Var g) a | Just (i, _) <- M.lookup g (iGlobals info), g `S.member` iKnown info, not (M.member g env) ->
    sub a $ \va -> bindRhs (RCallKnown i va)
  App f a -> sub f $ \vf -> sub a $ \va -> bindRhs (RCall vf va)
  Con c _ args -> do
    (tag, _, _) <- con c
    subs args $ \vs -> bindRhs (RAlloc tag vs)
  Case e alts -> sub e $ \ve -> do
    x <- fresh
    let tys = case typeOf info env e of
          TData _ as -> as
          _ -> []
    bs <- forM alts $ \(c, xs, b) -> do
      (tag, d, fields) <- con c
      let inst = substTy (M.fromList (zip (M.findWithDefault [] d (iParams info)) tys)) M.empty
          env' = M.union (M.fromList (zip xs (map inst fields))) env
      body <- expr info env' b (pure . Ret)
      pure (tag, foldr (\(i, y) rest -> Bind y (RField ve i) rest) body (zip [0 ..] xs))
    BindCase x ve (sortOn fst bs) <$> k (AVar x)
  Box e -> expr info env e k
  Unbox e -> expr info env e k
  Pair a b -> subs [a, b] $ \vs -> bindRhs (RAlloc 0 vs)
  LetPair x y e b -> sub e $ \ve -> do
    let (tx, ty) = case typeOf info env e of
          TPair p q -> (p, q)
          _ -> (TUnit, TUnit)
    rest <- expr info (M.insert x tx (M.insert y ty env)) b k
    pure (Bind x (RField ve 0) (Bind y (RField ve 1) rest))
  Cocase d _ bs -> do
    let obs = M.findWithDefault [] d (iObs info)
        ordered = [fromMaybe UnitLit (lookup o bs) | (o, _) <- obs]
        fvs = S.toList (S.unions (map freeVars ordered) `S.difference` M.keysSet (iGlobals info))
        base = length obs
        envB = M.fromList [(v, t) | v <- fvs, Just t <- [M.lookup v env]]
    is <- forM (zip obs ordered) $ \((o, _), e) -> do
      body <- expr info envB e (pure . Ret)
      liftFun info (Fun (d ++ "." ++ o) "%self" base fvs body)
    bindRhs (RCodata is fvs)
  Proj e o -> sub e $ \ve -> case typeOf info env e of
    TData d _ | Just i <- elemIndex o (map fst (M.findWithDefault [] d (iObs info))) -> bindRhs (RProj ve i)
    t -> lift (Left ("observation " ++ o ++ " on " ++ prettyTy t))
  Perform "out" a -> sub a $ \va -> bindRhs (ROut va)
  Perform op _ -> unsupported ("operation " ++ op ++ " (effect handlers are milestone M3)")
  Handle {} -> unsupported "effect handlers (milestone M3)"
  _ -> unsupported (takeWhile (/= ' ') (show tm))
  where
    sub e = expr info env e
    subs es kk = go es []
      where
        go [] acc = kk (reverse acc)
        go (e : rest) acc = sub e $ \v -> go rest (v : acc)

    branch env' e = expr info env' e (pure . Ret)

    bindRhs rhs = do
      x <- fresh
      Bind x rhs <$> k (AVar x)

    con c = maybe (lift (Left ("unknown constructor " ++ c))) pure (M.lookup c (iCons info))

    -- Lift the λ to a numbered function capturing its free locals.
    closure x t b = do
      let fvs = S.toList (freeVars b `S.difference` S.insert x (M.keysSet (iGlobals info)))
          env' = M.insert x t (M.fromList [(v, ty) | v <- fvs, Just ty <- [M.lookup v env]])
      body <- expr info env' b (pure . Ret)
      i <- liftFun info (Fun ("λ" ++ x) x 1 fvs body)
      bindRhs (RClosure i fvs)

-- | The type of a well-typed term (effects omitted: lowering doesn't need them).
typeOf :: Info -> Env -> Term -> Ty
typeOf info env tm = case tm of
  Var x -> fromMaybe TUnit (M.lookup x env <|> (snd <$> M.lookup x (iGlobals info)))
  UnitLit -> TUnit
  BoolLit _ -> TBool
  IntLit t _ -> TInt t
  Prim Eq _ _ -> TBool
  Prim Lt _ _ -> TBool
  Prim (Arith Optional _) a _ -> TData "Option" [go a]
  Prim _ a _ -> go a
  If _ a _ -> go a
  Lam x t b -> TFun t S.empty (typeOf info (M.insert x t env) b)
  LLam x t b -> TLFun t S.empty (typeOf info (M.insert x t env) b)
  App f _ -> case go f of
    TFun _ _ r -> r
    TLFun _ _ r -> r
    _ -> TUnit
  Let x e b -> typeOf info (M.insert x (go e) env) b
  Con c tys _ -> case M.lookup c (iCons info) of
    Just (_, d, _) -> TData d tys
    Nothing -> TUnit
  Case e ((c, xs, b) : _) -> case (go e, M.lookup c (iCons info)) of
    (TData _ tys, Just (_, d, fields)) ->
      let inst = substTy (M.fromList (zip (M.findWithDefault [] d (iParams info)) tys)) M.empty
       in typeOf info (M.union (M.fromList (zip xs (map inst fields))) env) b
    _ -> TUnit
  Box e -> TBox (go e)
  Unbox e -> case go e of
    TBox t -> t
    t -> t
  Pair a b -> TPair (go a) (go b)
  LetPair x y e b -> case go e of
    TPair p q -> typeOf info (M.insert x p (M.insert y q env)) b
    _ -> TUnit
  Cocase d tys _ -> TData d tys
  Proj e o -> case go e of
    TData d tys
      | Just t <- lookup o (M.findWithDefault [] d (iObs info)) ->
          substTy (M.fromList (zip (M.findWithDefault [] d (iParams info)) tys)) M.empty t
    _ -> TUnit
  Perform op _ -> M.findWithDefault TUnit op (iOps info)
  Handle _ e _ -> go e
  _ -> TUnit
  where
    go = typeOf info env

-- | Free variables of a term (locals and globals alike; callers remove globals).
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
