-- | Call-by-value, environment-based evaluator for Keel Core, stages 1–4
-- (spec/core.md §1.4, §2.5, §3.4, §4.5). Types are erased: @f[τ̄]@ evaluates like @f@. Runs core programs; elaborate λK₃ first. Assumes a well-typed program; stuck states are impossible by
-- Theorem 1.
module Keel.Eval (Value (..), Outcome (..), evalProgram) where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Monad.Trans.State.Strict (State, modify, runState)
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Data.Map.Strict qualified as M
import Keel.Syntax

data Value
  = VUnit
  | VInt IntTy Integer
  | VBool Bool
  | VClo Env String Term -- ^ ⟨ρ, x, e⟩, for both λ and λ° (linearity is erased)
  | VCon String [Value]
  | VBox Value
  | VPair Value Value
  | VCodata Env (M.Map String Term) -- ^ a cocase: each observation runs its branch in the env

type Env = M.Map String Value

instance Show Value where
  show v = case v of
    VUnit -> "()"
    VInt _ n -> show n
    VBool b -> if b then "true" else "false"
    VClo {} -> "<closure>"
    VCon c [] -> c
    VCon c vs -> c ++ "(" ++ commas (map show vs) ++ ")"
    VBox a -> "box " ++ show a
    VPair a b -> "(" ++ show a ++ ", " ++ show b ++ ")"
    VCodata {} -> "<codata>"
    where
      commas = foldr1 (\a b -> a ++ ", " ++ b)

-- | Structural equality on first-order values; closures are never equal.
instance Eq Value where
  VUnit == VUnit = True
  VInt t a == VInt u b = t == u && a == b
  VBool a == VBool b = a == b
  VCon c vs == VCon d ws = c == d && vs == ws
  VBox a == VBox b = a == b
  VPair a b == VPair c d = a == c && b == d
  _ == _ = False

-- | How a program ended. A panic stops the whole program (the reset handler of notes.md §16
-- lives outside Keel Core).
data Outcome = Done Value | Panicked String
  deriving (Eq, Show)

-- | Evaluation can panic and appends output text, in reversed chunks.
type Run = ExceptT String (State [String])

-- | A handler frame: operation ↦ (parameter, clause body), and the clause environment.
data Handler = Handler (M.Map String (String, Term)) Env

-- | Run @main@; returns the outcome and the values written with the built-in @out@ operation.
evalProgram :: Program -> (Outcome, String)
evalProgram (Program decls main) = (either Panicked Done r, concat (reverse trace))
  where
    (r, trace) = runState (runExceptT (eval [] globals main)) []
    -- ρ_Σ: the recursive knot of top-level definitions. Their bodies are effect-free (checked).
    globals = M.fromList [(f, pureValue (eval [] globals e)) | Def f _ e <- decls]
    pureValue m = case runState (runExceptT m) [] of
      (Right v, []) -> v
      _ -> stuck "effectful top-level definition"

-- | @hs@ is the handler stack, innermost first. Evaluation order is CBV: every subterm runs in
-- the monad, left to right, before its value is used.
eval :: [Handler] -> Env -> Term -> Run Value
eval hs env tm = case tm of
  At _ e -> eval hs env e
  Var x -> pure (env M.! x)
  TyApp f _ _ -> pure (env M.! f)
  UnitLit -> pure VUnit
  IntLit t n -> pure (VInt t n)
  BoolLit b -> pure (VBool b)
  Convert to e -> do
    v <- eval hs env e
    case v of
      VInt _ n -> let (lo, hi) = intRange to in pure (VInt to (lo + (n - lo) `mod` (hi - lo + 1)))
      _ -> stuck "conversion of a non-integer"
  Prim op a b -> do
    va <- eval hs env a
    vb <- eval hs env b
    prim op va vb
  If c a b -> do
    vc <- eval hs env c
    case vc of
      VBool True -> eval hs env a
      _ -> eval hs env b
  Lam x _ body -> pure (VClo env x body)
  LLam x _ body -> pure (VClo env x body)
  App f a -> do
    vf <- eval hs env f
    va <- eval hs env a
    case vf of
      -- The body runs under the handlers active at the call (deep handlers).
      VClo cenv x body -> eval hs (M.insert x va cenv) body
      _ -> stuck "application of a non-closure"
  Let x e body -> do
    v <- eval hs env e
    eval hs (M.insert x v env) body
  Con c _ args -> VCon c <$> mapM (eval hs env) args
  Case e alts -> do
    v <- eval hs env e
    case v of
      VCon c vs
        | (xs, body) : _ <- [(xs, body) | (c', xs, body) <- alts, c' == c] ->
            eval hs (M.union (M.fromList (zip xs vs)) env) body
      _ -> stuck "case without a matching constructor"
  Box e -> VBox <$> eval hs env e
  Unbox e -> do
    v <- eval hs env e
    case v of
      VBox a -> pure a
      _ -> stuck "unbox of a non-box"
  Perform op a -> do
    v <- eval hs env a
    perform hs op v
  Handle _ body clauses ->
    let frame = Handler (M.fromList [(op, (x, e)) | (op, x, e) <- clauses]) env
     in eval (frame : hs) env body
  Pair a b -> VPair <$> eval hs env a <*> eval hs env b
  LetPair x y e body -> do
    v <- eval hs env e
    case v of
      VPair a b -> eval hs (M.insert y b (M.insert x a env)) body
      _ -> stuck "let-pair of a non-pair"
  Cocase _ _ branches -> pure (VCodata env (M.fromList branches))
  Proj e o -> do
    v <- eval hs env e
    case v of
      VCodata cenv bs | Just b <- M.lookup o bs -> eval hs cenv b
      _ -> stuck ("observation " ++ o ++ " of a non-codata value")
  _ -> stuck ("surface construct in core: " ++ show tm)

-- | Find the innermost handler for @op@ and run its clause with the handlers *outside* it,
-- so a clause performing the same operation reaches the next handler out. The clause's value
-- is the operation's result: tail-resumptive, so no continuation is captured.
perform :: [Handler] -> String -> Value -> Run Value
perform hs op v = case break handles hs of
  (_, Handler clauses cenv : outer) | Just (x, body) <- M.lookup op clauses ->
    eval outer (M.insert x v cenv) body
  _ -> machine op v
  where
    handles (Handler clauses _) = M.member op clauses

-- | Operations no handler caught are performed by the machine. The evaluator has no device
-- memory, so an unhandled MMIO operation panics (handle MMIO with a mock to run drivers here).
machine :: String -> Value -> Run Value
machine "out" (VInt _ n) = lift (modify ((show n ++ "\n") :)) >> pure VUnit
machine "putc" (VInt _ b) = lift (modify ([toEnum (fromInteger b)] :)) >> pure VUnit
machine op _ = throwE ("unhandled operation " ++ op ++ " (no device memory in the evaluator)")

prim :: Prim -> Value -> Value -> Run Value
prim op (VInt t a) (VInt _ b) = case op of
  Eq -> pure (VBool (a == b))
  Lt -> pure (VBool (a < b))
  Bits bop ->
    -- Canonical values: and/or/xor stay in range; a left shift wraps to the width; shifting
    -- right is arithmetic on signed values (Integer shiftR) and logical on unsigned ones.
    let (lo, hi) = intRange t
        wrap r = lo + (r - lo) `mod` (hi - lo + 1)
        amount = fromInteger (max 0 (min 64 b))
     in pure . VInt t $ case bop of
          And -> a .&. b
          Or -> a .|. b
          Xor -> xor a b
          Shl -> wrap (a `shiftL` amount)
          Shr -> a `shiftR` amount
  Arith _ aop | aop `elem` [Div, Rem], b == 0 -> throwE "division by zero"
  Arith ov aop ->
    let r = arith aop a b
        (lo, hi) = intRange t
     in if r >= lo && r <= hi
          then pure (if ov == Optional then VCon "Some" [VInt t r] else VInt t r)
          else case ov of
            Optional -> pure (VCon "None" [])
            Checked -> throwE ("arithmetic overflow: " ++ show a ++ sym aop ++ show b ++ " in " ++ prettyTy (TInt t))
            Wrap -> pure (VInt t (lo + (r - lo) `mod` (hi - lo + 1)))
            Saturate -> pure (VInt t (max lo (min hi r)))
  where
    sym Add = " + "
    sym Sub = " - "
    sym Mul = " * "
    sym Div = " / "
    sym Rem = " % "
    arith Div = quot
    arith Rem = rem
    arith Add = (+)
    arith Sub = (-)
    arith Mul = (*)
prim _ _ _ = stuck "primitive on non-integers"

stuck :: String -> a
stuck msg = error ("stuck (ill-typed program?): " ++ msg)
