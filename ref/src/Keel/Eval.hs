-- | Call-by-value, environment-based evaluator for Keel Core, stages 1–4
-- (spec/core.md §1.4, §2.5, §3.4, §4.5). Types are erased: @f[τ̄]@ evaluates like @f@. Runs core programs; elaborate λK₃ first. Assumes a well-typed program; stuck states are impossible by
-- Theorem 1.
module Keel.Eval (Value (..), Outcome (..), Machine (..), evalProgram, evalProgramWith, evalProgramOn, runProgramOn) where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Monad.Trans.State.Strict (State, get, modify, put, runState)
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Data.Map.Strict qualified as M
import Data.Sequence qualified as Seq
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
  | VArray (Seq.Seq Value)

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
    VArray xs -> "[" ++ (if null xs then "" else commas (map show (toList xs))) ++ "]"
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
  VArray xs == VArray ys = xs == ys
  _ == _ = False

-- | How a program ended. A panic stops the whole program (the reset handler of notes.md §16
-- lives outside Keel Core).
data Outcome = Done Value | Panicked String
  deriving (Eq, Show)

-- | What a program sees of the world: the bytes @getc@ reads, the files @openFile@ can
-- open (bytes as characters; Nothing if a path can't be opened), and whether it is hosted:
-- it has a network and can write files.
data Machine = Machine {mInput :: String, mFiles :: FilePath -> Maybe String, mHosted :: Bool}

-- | Evaluation can panic, and changes the world: input not yet read, output written (newest
-- chunk first), the open files' unread bytes by handle, the files written (Nothing: none can
-- be) and the handles writing them, and the network (if there is one).
data World = World {wInput :: String, wOutput :: [String], wFiles :: FilePath -> Maybe String, wOpen :: M.Map Integer String, wWritten :: Maybe (M.Map FilePath String), wWriting :: M.Map Integer FilePath, wNet :: Maybe Net}

-- | A loopback network, all inside the program: listeners by fd (port, connections waiting to
-- be accepted), connected sockets by fd, the next fd and free port, and a clock that only
-- moves when pollWait waits.
data Net = Net {nListeners :: M.Map Integer (Integer, [Integer]), nSocks :: M.Map Integer Sock, nNext :: Integer, nPort :: Integer, nClock :: Integer}

-- | A connected socket: its peer, the bytes that arrived, and whether the peer has closed.
data Sock = Sock {sPeer :: Integer, sInbox :: String, sPeerClosed :: Bool}

type Run = ExceptT String (State World)

-- | A handler frame: operation ↦ (parameter, clause body), and the clause environment.
data Handler = Handler (M.Map String (String, Term)) Env

-- | Run @main@ with no input; returns the outcome and what it wrote with @out@ and @putc@.
evalProgram :: Program -> (Outcome, String)
evalProgram = evalProgramWith ""

-- | Run @main@ with the bytes @getc@ reads (as characters), and no files.
evalProgramWith :: String -> Program -> (Outcome, String)
evalProgramWith input = evalProgramOn (Machine input (const Nothing) False)

evalProgramOn :: Machine -> Program -> (Outcome, String)
evalProgramOn m p = let (o, out, _) = runProgramOn m p in (o, out)

-- | Also the files the program wrote, with their contents at the end (keelc run saves them).
runProgramOn :: Machine -> Program -> (Outcome, String, M.Map FilePath String)
runProgramOn (Machine input files hosted) (Program decls main) = (either Panicked Done r, concat (reverse (wOutput w)), fromMaybe M.empty (wWritten w))
  where
    (r, w) = runState (runExceptT (eval [] globals main)) (World input [] files M.empty (if hosted then Just M.empty else Nothing) M.empty (if hosted then Just (Net M.empty M.empty 3 49152 0) else Nothing))
    -- ρ_Σ: the recursive knot of top-level definitions. Their bodies are effect-free (checked).
    globals = M.fromList [(f, pureValue (eval [] globals e)) | Def f _ e <- decls]
    pureValue m = case runState (runExceptT m) (World "" [] (const Nothing) M.empty Nothing M.empty Nothing) of
      (Right v, World _ [] _ _ _ _ _) -> v
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
  ArrayPrim AArena _ [f] -> eval hs env (App f UnitLit)
  ArrayPrim op _ args -> mapM (eval hs env) args >>= array op
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
machine "out" (VInt _ n) = write (show n ++ "\n")
machine "putc" (VInt _ b) = write [toEnum (fromInteger b)]
machine "getc" _ = do
  w <- lift get
  case wInput w of
    c : rest -> lift (put w {wInput = rest}) >> pure (byte c)
    [] -> pure (VInt i64 (-1))
-- Handles count up from 3, like file descriptors after stdin, stdout and stderr. A file the
-- program wrote is read as it wrote it.
machine "openFile" (VArray path) = do
  w <- lift get
  let name = pathOf path
  case contents w name of
    Just bytes -> lift (put w {wOpen = M.insert (nextHandle w) bytes (wOpen w)}) >> pure (VInt i64 (nextHandle w))
    Nothing -> pure (VInt i64 (-1))
machine op (VArray path) | op `elem` ["createFile", "appendFile"] = do
  w <- lift get
  let name = pathOf path
      start = if op == "createFile" then "" else fromMaybe "" (contents w name)
  case wWritten w of
    Just written -> do
      lift (put w {wWritten = Just (M.insert name start written), wWriting = M.insert (nextHandle w) name (wWriting w)})
      pure (VInt i64 (nextHandle w))
    Nothing -> pure (VInt i64 (-1))
machine "writeBytes" (VPair (VInt _ h) (VArray bytes)) = do
  w <- lift get
  case (M.lookup h (wWriting w), wWritten w) of
    (Just name, Just written) -> do
      let text = [toEnum (fromInteger b) | VInt _ b <- toList bytes]
      lift (put w {wWritten = Just (M.adjust (++ text) name written)})
      pure (VInt i64 (toInteger (length text)))
    _ -> throwE "writeBytes on a handle that isn't open for writing"
machine "readByte" (VInt _ h) = do
  w <- lift get
  case M.lookup h (wOpen w) of
    Just (c : rest) -> lift (put w {wOpen = M.insert h rest (wOpen w)}) >> pure (byte c)
    Just [] -> pure (VInt i64 (-1))
    Nothing -> throwE "readByte on a handle that isn't open"
machine "closeFile" (VInt _ h) = lift (modify (\w -> w {wOpen = M.delete h (wOpen w), wWriting = M.delete h (wWriting w)})) >> pure VUnit
machine op v | op `elem` [o | (l, os) <- builtinEffects, l == netE, (o, _, _) <- os] = do
  w <- lift get
  case wNet w of
    Nothing -> pure (netFailure op)
    Just n -> do
      (r, n') <- either throwE pure (network op v n)
      lift (put w {wNet = Just n'})
      pure r
machine op _ = throwE ("unhandled operation " ++ op ++ " (no device memory in the evaluator)")

pathOf :: Seq.Seq Value -> FilePath
pathOf path = [toEnum (fromInteger b) | VInt _ b <- toList path]

-- | A file's bytes as the program sees them: as it wrote them, else as the machine has them.
contents :: World -> FilePath -> Maybe String
contents w name = maybe (wFiles w name) Just (wWritten w >>= M.lookup name)

nextHandle :: World -> Integer
nextHandle w = maybe 3 (+ 1) (max (fst <$> M.lookupMax (wOpen w)) (fst <$> M.lookupMax (wWriting w)))

-- | What a Net operation gives without a network (RISC-V): it fails.
netFailure :: String -> Value
netFailure op = case op of
  "sockRecv" -> VArray Seq.empty
  "sockClose" -> VUnit
  "clockMs" -> VInt i64 0
  "pollWait" -> VInt i64 (-2)
  _ -> VInt i64 (-1)

-- | A Net operation on the loopback model. The native runtime does the same with sockets; a
-- program sees the same events as long as it doesn't depend on how bytes are split into
-- receives.
network :: String -> Value -> Net -> Either String (Value, Net)
network op v n = case (op, v) of
  ("tcpListen", VPair _ (VInt _ p))
    | p /= 0, p `elem` map fst (M.elems (nListeners n)) -> pure (int (-1), n)
    | otherwise ->
        let port = if p == 0 then nPort n else p
         in pure (int (nNext n), n {nListeners = M.insert (nNext n) (port, []) (nListeners n), nNext = nNext n + 1, nPort = nPort n + (if p == 0 then 1 else 0)})
  ("sockPort", VInt _ fd) -> pure (int (maybe (-1) fst (M.lookup fd (nListeners n))), n)
  ("tcpAccept", VInt _ fd) -> case M.lookup fd (nListeners n) of
    Just (port, c : rest) -> pure (int c, n {nListeners = M.insert fd (port, rest) (nListeners n)})
    _ -> pure (int (-1), n)
  ("tcpConnect", VPair _ (VInt _ p)) -> case [fd | (fd, (port, _)) <- M.toList (nListeners n), port == p] of
    l : _ ->
      let a = nNext n
          b = a + 1
          (port, waiting) = nListeners n M.! l
       in pure (int a, n {nSocks = M.insert a (Sock b "" False) (M.insert b (Sock a "" False) (nSocks n)), nListeners = M.insert l (port, waiting ++ [b]) (nListeners n), nNext = b + 1})
    [] -> pure (int (-1), n)
  ("sockSend", VPair (VInt _ fd) (VPair (VArray bytes) (VInt _ from))) -> case M.lookup fd (nSocks n) of
    Just s | not (sPeerClosed s), Just peer <- M.lookup (sPeer s) (nSocks n) ->
      let room = max 0 (buffer - length (sInbox peer))
          text = [toEnum (fromInteger b) | VInt _ b <- toList (Seq.take room (Seq.drop (fromInteger from) bytes))]
       in pure (int (toInteger (length text)), n {nSocks = M.insert (sPeer s) peer {sInbox = sInbox peer ++ text} (nSocks n)})
    _ -> pure (int (-1), n)
  ("sockRecv", VInt _ fd) -> case M.lookup fd (nSocks n) of
    Just s -> pure (VArray (Seq.fromList (map byte (sInbox s))), n {nSocks = M.insert fd s {sInbox = ""} (nSocks n)})
    Nothing -> pure (VArray Seq.empty, n)
  ("sockClose", VInt _ fd) ->
    let socks = case M.lookup fd (nSocks n) of
          Just s -> M.adjust (\p -> p {sPeerClosed = True}) (sPeer s) (M.delete fd (nSocks n))
          Nothing -> nSocks n
     in pure (VUnit, n {nSocks = socks, nListeners = M.delete fd (nListeners n)})
  ("pollWait", VPair (VArray fds) (VInt _ timeout)) ->
    case [i * 4 + r | (i, VInt _ e) <- zip [0 ..] (toList fds), let r = readiness (e `div` 4) (odd e) (odd (e `div` 2)), r /= 0] of
      i : _ -> pure (int i, n)
      []
        | timeout < 0 -> Left "pollWait would wait forever (no socket can become ready)"
        | otherwise -> pure (int (-1), n {nClock = nClock n + timeout})
  ("clockMs", _) -> pure (int (nClock n), n)
  _ -> Left ("bad Net operation " ++ op)
  where
    int = VInt i64
    -- Each socket receives into a buffer this size: a sender to a full one waits.
    buffer = 65536
    -- As poll: readable (1) is a listener with a connection waiting or a socket with bytes, if
    -- asked, and always a closed peer (POLLHUP) or an fd that isn't open (POLLNVAL); writable
    -- (2), if asked, is room in the peer's buffer.
    readiness fd wantsRead wantsWrite = case (M.lookup fd (nListeners n), M.lookup fd (nSocks n)) of
      (Just (_, waiting), _) -> if wantsRead && not (null waiting) then 1 else 0
      (_, Just s) ->
        (if (wantsRead && not (null (sInbox s))) || sPeerClosed s then 1 else 0)
          + (if wantsWrite && maybe False ((< buffer) . length . sInbox) (M.lookup (sPeer s) (nSocks n)) then 2 else 0)
      _ -> 1 :: Integer

-- | Arrays are values: an update returns a new sequence (the native code updates in place
-- when it can, which no program can observe).
array :: ArrayOp -> [Value] -> Run Value
array op args = case (op, args) of
  (AEmpty, []) -> pure (VArray Seq.empty)
  (ANew, [VInt _ n, x]) | n >= 0 -> pure (VArray (Seq.replicate (fromInteger n) x))
  (ANew, _) -> outOfBounds
  (ALength, [VArray xs]) -> pure (VInt i64 (toInteger (Seq.length xs)))
  (AGet, [VArray xs, VInt _ i]) -> maybe outOfBounds pure (Seq.lookup (fromInteger i) xs)
  (ASet, [VArray xs, VInt _ i, x])
    | i >= 0 && i < toInteger (Seq.length xs) -> pure (VArray (Seq.update (fromInteger i) x xs))
    | otherwise -> outOfBounds
  (APush, [VArray xs, x]) -> pure (VArray (xs Seq.|> x))
  (APop, [VArray xs]) -> case Seq.viewr xs of
    rest Seq.:> _ -> pure (VArray rest)
    Seq.EmptyR -> outOfBounds
  _ -> stuck "array operation on a non-array"
  where
    outOfBounds = throwE "array index out of bounds"

write :: String -> Run Value
write s = lift (modify (\w -> w {wOutput = s : wOutput w})) >> pure VUnit

byte :: Char -> Value
byte c = VInt i64 (toInteger (fromEnum c))

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
