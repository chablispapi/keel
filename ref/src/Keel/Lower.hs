-- | M0 lowering (notes.md §5, §17): monomorphic Keel Core → A-normal form → closure
-- conversion → a first-order IR that maps one-to-one onto assembly.
--
-- M0 covers the λ-calculus fragment: i64, Bool, Unit, arithmetic, comparisons, if, let,
-- λ / λ°, application, top-level definitions (recursive), and the built-in @out@. Data,
-- pairs, codata and handlers come in M1; anything else is reported as unsupported.
module Keel.Lower (Atom (..), Rhs (..), Expr (..), Fun (..), LProg (..), lower) where

import Control.Monad (forM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, put, runStateT)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.Syntax

data Atom
  = AInt Integer -- ^ integers, and Bool / Unit as 0 or 1
  | AVar String  -- ^ a local variable (stack slot)
  | AGlobal Int  -- ^ the static closure of top-level function i
  deriving (Show)

data Rhs
  = RAtom Atom
  | RPrim Prim Atom Atom
  | RCall Atom Atom           -- ^ call an unknown closure
  | RCallKnown Int Atom       -- ^ direct call to top-level function i (the video's "free" case)
  | RClosure Int [String]     -- ^ allocate a closure for function i capturing these locals
  | ROut Atom                 -- ^ print an integer
  deriving (Show)

data Expr
  = Ret Atom                          -- ^ the value of this expression
  | Bind String Rhs Expr              -- ^ let x = rhs in e
  | BindIf String Atom Expr Expr Expr -- ^ let x = (if a then e₁ else e₂) in e
  deriving (Show)

-- | A closure-converted function: called with its closure (holding @funEnv@ in order) and one
-- argument.
data Fun = Fun {funName :: String, funParam :: String, funEnv :: [String], funBody :: Expr}
  deriving (Show)

-- | Functions are numbered: top-level definitions first (in order), then lifted λs. @main@ is a
-- separate body.
data LProg = LProg {lFuns :: [Fun], lMain :: Expr}
  deriving (Show)

-- | Fresh-name counter and lifted functions (index ↦ function).
type M = StateT (Int, M.Map Int Fun) (Either String)

fresh :: M String
fresh = do
  (n, fs) <- get
  put (n + 1, fs)
  pure ("%t" ++ show n)

unsupported :: String -> M a
unsupported what = lift (Left ("not supported in M0: " ++ what))

-- | Lower a monomorphic core program (the output of "Keel.Mono".compile).
lower :: Program -> Either String LProg
lower (Program decls main) = do
  let defs = [(f, e) | Def f _ e <- decls]
      globals = M.fromList (zip (map fst defs) [0 ..])
      lifted0 = length defs
  ((tops, mainE), (_, liftedFs)) <-
    runStateT
      ( do
          tops <- forM (zip [0 ..] defs) $ \(i, (f, e)) -> case e of
            Lam x _ b -> topFun globals i f x b
            LLam x _ b -> topFun globals i f x b
            _ -> unsupported ("top-level definition " ++ f ++ " that is not a λ")
          m <- expr globals main (pure . Ret)
          pure (tops, m)
      )
      (0, M.empty)
  let funs = tops ++ [liftedFs M.! i | i <- [lifted0 .. lifted0 + M.size liftedFs - 1]]
  pure (LProg funs mainE)

-- | A top-level λ: no environment, since definitions are closed apart from other globals.
topFun :: M.Map String Int -> Int -> String -> String -> Term -> M Fun
topFun globals _ f x b = do
  body <- expr globals b (pure . Ret)
  pure (Fun f x [] body)

-- | CPS-style ANF conversion: @k@ receives an atom for the value of the term.
expr :: M.Map String Int -> Term -> (Atom -> M Expr) -> M Expr
expr globals tm k = case tm of
  Var x -> k (maybe (AVar x) AGlobal (M.lookup x globals))
  UnitLit -> k (AInt 0)
  BoolLit b -> k (AInt (if b then 1 else 0))
  IntLit t n
    | t == i64 -> k (AInt n)
    | otherwise -> unsupported ("integer type " ++ prettyTy (TInt t) ++ " (M0 has i64 only)")
  Prim op a b -> do
    case op of
      Arith Saturate _ -> unsupported "saturating arithmetic"
      Arith Optional _ -> unsupported "+? (needs data types)"
      _ -> pure ()
    expr globals a $ \va -> expr globals b $ \vb -> bindRhs (RPrim op va vb)
  Let x e b -> expr globals e $ \v -> Bind x (RAtom v) <$> expr globals b k
  If c a b -> expr globals c $ \vc -> do
    x <- fresh
    ea <- expr globals a (pure . Ret)
    eb <- expr globals b (pure . Ret)
    BindIf x vc ea eb <$> k (AVar x)
  Lam x _ b -> closure x b
  LLam x _ b -> closure x b
  App (Var g) a | Just i <- M.lookup g globals -> expr globals a $ \va -> bindRhs (RCallKnown i va)
  App f a -> expr globals f $ \vf -> expr globals a $ \va -> bindRhs (RCall vf va)
  Perform "out" a -> expr globals a $ \va -> bindRhs (ROut va)
  Perform op _ -> unsupported ("operation " ++ op ++ " (handlers come in M1)")
  Handle {} -> unsupported "effect handlers"
  _ -> unsupported (takeWhile (/= ' ') (show tm))
  where
    bindRhs rhs = do
      x <- fresh
      Bind x rhs <$> k (AVar x)

    -- Lift the λ to a numbered function capturing its free locals.
    closure x b = do
      let fvs = S.toList (freeVars b `S.difference` S.insert x (M.keysSet globals))
      body <- expr globals b (pure . Ret)
      (n, fs) <- get
      let i = M.size globals + M.size fs
      put (n, M.insert i (Fun ("λ" ++ x) x fvs body) fs)
      bindRhs (RClosure i fvs)

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
