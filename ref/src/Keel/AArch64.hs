-- | M0 code generator: the lowered IR ("Keel.Lower") → Apple ARM64 assembly (Mach-O), to be
-- assembled and linked with the system @cc@ (notes.md §12, §17).
--
-- Deliberately simple: every variable lives in a stack slot and values pass through scratch
-- registers x9–x16, so nothing needs saving across calls.
-- ponytail: no register allocation, no tail calls (deep recursion uses stack); both are M4.
--
-- Conventions: a closure is a heap block @[code pointer, captured values…]@. Every function is
-- called with the closure in x0 and its argument in x1, and returns its result in x0. Bool and
-- Unit are 0/1 and 0. Closures come from a never-freed bump arena; running out is a panic.
module Keel.AArch64 (compileNative, emitProgram) where

import Control.Monad (forM_, when)
import Control.Monad.Trans.State.Strict (State, execState, get, modify, put)
import Data.Bits (shiftR, (.&.))
import Data.List (nub)
import Data.Map.Strict qualified as M
import Keel.Check (checkProgram)
import Keel.Lower
import Keel.Mono (compile)
import Keel.Syntax

-- | The whole M0 pipeline: check, elaborate, monomorphize, lower, emit.
compileNative :: Program -> Either String String
compileNative p = do
  mono <- either (Left . show) Right (compile p)
  (t, _) <- either (Left . show) Right (checkProgram mono)
  lp <- lower mono
  pure (emitProgram t lp)

heapSize :: Integer
heapSize = 16 * 1024 * 1024

-- | Label counter and emitted lines (reversed).
type G = State (Int, [String])

line :: String -> G ()
line l = modify (\(n, ls) -> (n, l : ls))

ins :: String -> G ()
ins i = line ("\t" ++ i)

newLabel :: G String
newLabel = do
  (n, ls) <- get
  put (n + 1, ls)
  pure ("Lk" ++ show n)

-- | Emit a program whose @main@ has type @mainTy@: functions, @main@, runtime support, data.
emitProgram :: Ty -> LProg -> String
emitProgram mainTy (LProg funs mainE) = unlines (reverse (snd (execState gen (0, []))))
  where
    gen = do
      line "\t.section __TEXT,__text,regular,pure_instructions"
      forM_ (zip [0 :: Int ..] funs) $ \(i, f) -> emitFun ("_kf_" ++ show i) f
      emitFun "_kf_main" (Fun "main" "%unused" [] mainE)
      emitEntry mainTy
      emitRuntime
      line "\t.section __DATA,__data"
      line "\t.p2align 3"
      forM_ (zip [0 :: Int ..] funs) $ \(i, f) -> do
        line ("_kc_" ++ show i ++ ":\t\t\t// static closure of " ++ funName f)
        ins (".quad _kf_" ++ show i)
      line "_keel_heap_ptr:"
      ins ".quad _keel_heap"
      ins (".quad _keel_heap+" ++ show heapSize)
      line ("\t.zerofill __DATA,__bss,_keel_heap," ++ show heapSize ++ ",4")
      line "\t.section __TEXT,__cstring,cstring_literals"
      forM_ strings $ \(l, s) -> line (l ++ ":\t.asciz " ++ show s)

    strings =
      [ ("_keel_fmt_int", "%lld\n")
      , ("_keel_fmt_result", "result: %lld\n")
      , ("_keel_str_true", "result: true\n")
      , ("_keel_str_false", "result: false\n")
      , ("_keel_str_unit", "result: ()\n")
      , ("_keel_msg_overflow", overflowMsg)
      , ("_keel_msg_oom", oomMsg)
      ]

overflowMsg, oomMsg :: String
overflowMsg = "panic: arithmetic overflow\n"
oomMsg = "panic: out of memory\n"

-- | A function with its stack frame: one 8-byte slot per variable.
emitFun :: String -> Fun -> G ()
emitFun lbl (Fun name x env body) = do
  let vars = nub (x : env ++ bound body)
      slots = M.fromList (zip vars [0 :: Int ..])
      frame = 16 * ((8 * length vars + 15) `div` 16)
  line "\t.p2align 2"
  line (lbl ++ ":\t\t\t// " ++ name)
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  when (frame > 0) $ subSp frame
  forM_ (zip [1 :: Int ..] env) $ \(j, v) -> do
    ins ("ldr x9, [x0, #" ++ show (8 * j) ++ "]")
    store slots "x9" v
  store slots "x1" x
  expr slots Nothing body

subSp :: Int -> G ()
subSp n
  | n < 4096 = ins ("sub sp, sp, #" ++ show n)
  | otherwise = movImm "x9" (toInteger n) >> ins "sub sp, sp, x9"

-- | Variables bound in a body.
bound :: Expr -> [String]
bound e = case e of
  Ret _ -> []
  Bind x _ rest -> x : bound rest
  BindIf x _ a b rest -> x : bound a ++ bound b ++ bound rest

slotOf :: M.Map String Int -> String -> String
slotOf slots v = "[sp, #" ++ show (8 * slots M.! v) ++ "]"

store, load' :: M.Map String Int -> String -> String -> G ()
store slots r v = ins ("str " ++ r ++ ", " ++ slotOf slots v)
load' slots r v = ins ("ldr " ++ r ++ ", " ++ slotOf slots v)

atom :: M.Map String Int -> String -> Atom -> G ()
atom slots r a = case a of
  AInt n -> movImm r n
  AVar v -> load' slots r v
  AGlobal i -> address r ("_kc_" ++ show i)

address :: String -> String -> G ()
address r sym = do
  ins ("adrp " ++ r ++ ", " ++ sym ++ "@PAGE")
  ins ("add " ++ r ++ ", " ++ r ++ ", " ++ sym ++ "@PAGEOFF")

-- | Load any 64-bit constant (two's complement) with movz/movk.
movImm :: String -> Integer -> G ()
movImm r n =
  case [(k, c) | (k, c) <- zip [0 :: Int ..] chunks, c /= 0] of
    [] -> ins ("mov " ++ r ++ ", #0")
    (k0, c0) : rest -> do
      ins ("movz " ++ r ++ ", #" ++ show c0 ++ shift k0)
      forM_ rest $ \(k, c) -> ins ("movk " ++ r ++ ", #" ++ show c ++ shift k)
  where
    u = n `mod` (2 ^ (64 :: Int))
    chunks = [(u `shiftR` (16 * k)) .&. 0xffff | k <- [0 .. 3]]
    shift k = if k == 0 then "" else ", lsl #" ++ show (16 * k)

-- | @join@ is Nothing in tail position (return), or the slot and label an if-branch delivers to.
expr :: M.Map String Int -> Maybe (String, String) -> Expr -> G ()
expr slots join e = case e of
  Ret a -> do
    atom slots "x0" a
    case join of
      Nothing -> do
        ins "mov sp, x29"
        ins "ldp x29, x30, [sp], #16"
        ins "ret"
      Just (v, lbl) -> do
        store slots "x0" v
        ins ("b " ++ lbl)
  Bind x rhs rest -> do
    rhsCode slots rhs
    store slots "x0" x
    expr slots join rest
  BindIf x c a b rest -> do
    lElse <- newLabel
    lJoin <- newLabel
    atom slots "x9" c
    ins ("cbz x9, " ++ lElse)
    expr slots (Just (x, lJoin)) a
    line (lElse ++ ":")
    expr slots (Just (x, lJoin)) b
    line (lJoin ++ ":")
    expr slots join rest

-- | Compute a right-hand side into x0.
rhsCode :: M.Map String Int -> Rhs -> G ()
rhsCode slots rhs = case rhs of
  RAtom a -> atom slots "x0" a
  RPrim op a b -> do
    atom slots "x9" a
    atom slots "x10" b
    case op of
      Arith Checked Add -> ins "adds x0, x9, x10" >> ins "b.vs _keel_panic_overflow"
      Arith Checked Sub -> ins "subs x0, x9, x10" >> ins "b.vs _keel_panic_overflow"
      Arith Checked Mul -> do
        -- the full product fits in 64 bits iff the high half is the sign-extension of the low
        ins "mul x0, x9, x10"
        ins "smulh x11, x9, x10"
        ins "cmp x11, x0, asr #63"
        ins "b.ne _keel_panic_overflow"
      Arith _ Add -> ins "add x0, x9, x10"
      Arith _ Sub -> ins "sub x0, x9, x10"
      Arith _ Mul -> ins "mul x0, x9, x10"
      Eq -> ins "cmp x9, x10" >> ins "cset x0, eq"
      Lt -> ins "cmp x9, x10" >> ins "cset x0, lt"
  RCall f a -> do
    atom slots "x0" f
    atom slots "x1" a
    ins "ldr x16, [x0]"
    ins "blr x16"
  RCallKnown i a -> do
    address "x0" ("_kc_" ++ show i)
    atom slots "x1" a
    ins ("bl _kf_" ++ show i)
  RClosure i fvs -> do
    let size = 8 * (1 + length fvs)
    address "x9" "_keel_heap_ptr"
    ins "ldr x0, [x9]"
    ins ("add x10, x0, #" ++ show size)
    ins "ldr x11, [x9, #8]"
    ins "cmp x10, x11"
    ins "b.hi _keel_panic_oom"
    ins "str x10, [x9]"
    address "x11" ("_kf_" ++ show i)
    ins "str x11, [x0]"
    forM_ (zip [1 :: Int ..] fvs) $ \(j, v) -> do
      load' slots "x11" v
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
  ROut a -> do
    -- Apple ARM64 passes variadic arguments on the stack.
    atom slots "x9" a
    ins "sub sp, sp, #16"
    ins "str x9, [sp]"
    address "x0" "_keel_fmt_int"
    ins "bl _printf"
    ins "add sp, sp, #16"
    ins "mov x0, #0"

-- | @_main@ runs the Keel main and prints its result as a last line.
emitEntry :: Ty -> G ()
emitEntry t = do
  line "\t.globl _main"
  line "\t.p2align 2"
  line "_main:"
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  ins "sub sp, sp, #16"
  ins "bl _kf_main"
  case t of
    TInt _ -> do
      ins "str x0, [sp]"
      address "x0" "_keel_fmt_result"
      ins "bl _printf"
    TBool -> do
      lFalse <- newLabel
      lDone <- newLabel
      ins ("cbz x0, " ++ lFalse)
      address "x0" "_keel_str_true"
      ins ("b " ++ lDone)
      line (lFalse ++ ":")
      address "x0" "_keel_str_false"
      line (lDone ++ ":")
      ins "bl _printf"
    TUnit -> address "x0" "_keel_str_unit" >> ins "bl _printf"
    _ -> pure ()
  ins "mov x0, #0"
  ins "mov sp, x29"
  ins "ldp x29, x30, [sp], #16"
  ins "ret"

-- | Panics write a message to stderr and exit with status 101. C @exit@ flushes stdout first,
-- so output written before the panic is kept (spec §2.5).
emitRuntime :: G ()
emitRuntime = do
  panic "_keel_panic_overflow" "_keel_msg_overflow" (length overflowMsg)
  panic "_keel_panic_oom" "_keel_msg_oom" (length oomMsg)
  where
    panic lbl msg len = do
      line "\t.p2align 2"
      line (lbl ++ ":")
      ins "mov x0, #2"
      address "x1" msg
      ins ("mov x2, #" ++ show len)
      ins "bl _write"
      ins "mov x0, #101"
      ins "bl _exit"
