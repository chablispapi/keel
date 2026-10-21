-- | Code generator: the lowered IR ("Keel.Lower") → Apple ARM64 assembly (Mach-O), assembled
-- and linked with the system @cc@ (notes.md §12, §17).
--
-- Deliberately simple: every variable lives in a stack slot and values pass through scratch
-- registers x9–x16, so nothing needs saving across calls.
-- ponytail: no register allocation (M4); a call in tail position reuses the frame, so loops
-- written as tail recursion run in constant stack.
--
-- Conventions: every function is called with its closure (or codata block) in x0 and its
-- argument in x1, and returns its result in x0. Heap blocks come from a never-freed bump
-- arena; running out is a panic. Panics exit with status 101 after flushing stdout.
module Keel.AArch64 (compileNative, emitProgram) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Data.Bits (shiftR, (.&.))
import Data.List (nub)
import Data.Map.Strict qualified as M
import Keel.Check (checkProgram)
import Keel.Lower
import Keel.Mono (compile)
import Keel.Syntax

-- | The whole pipeline: check, elaborate, monomorphize, lower, emit.
compileNative :: Program -> Either String String
compileNative p = do
  mono <- either (Left . show) Right (compile p)
  (t, _) <- either (Left . show) Right (checkProgram mono)
  lp <- lower mono
  let Program decls _ = mono
  pure (emitProgram (optionDecl : decls) t lp)

heapSize :: Integer
heapSize = 64 * 1024 * 1024

data GS = GS {gsLabel :: Int, gsLines :: [String], gsStrings :: M.Map String String}

type G = State GS

line :: String -> G ()
line l = modify (\s -> s {gsLines = l : gsLines s})

ins :: String -> G ()
ins i = line ("\t" ++ i)

newLabel :: G String
newLabel = do
  n <- gets gsLabel
  modify (\s -> s {gsLabel = n + 1})
  pure ("Lk" ++ show n)

-- | Intern a C string and return its label.
str :: String -> G String
str s = do
  m <- gets gsStrings
  case M.lookup s m of
    Just l -> pure l
    Nothing -> do
      let l = "_keel_s" ++ show (M.size m)
      modify (\st -> st {gsStrings = M.insert s l m})
      pure l

-- | printf a constant string (no arguments).
printStr :: String -> G ()
printStr s = do
  l <- str (concatMap (\c -> if c == '%' then "%%" else [c]) s)
  address "x0" l
  ins "bl _printf"

-- | Emit a program whose @main@ has type @mainTy@.
emitProgram :: [Decl] -> Ty -> LProg -> String
emitProgram decls mainTy (LProg funs statics mainE) = unlines (reverse (gsLines (execState gen (GS 0 [] M.empty))))
  where
    printers = printerTypes decls mainTy
    gen = do
      line "\t.section __TEXT,__text,regular,pure_instructions"
      forM_ (M.toList funs) $ \(i, f) -> emitFun ("_kf_" ++ show i) f
      emitFun "_kf_main" (Fun "main" "%unused" 1 [] mainE)
      emitEntry printers mainTy
      forM_ (M.toList printers) $ \(_, (t, lbl)) -> emitPrinter decls printers lbl t
      emitRuntime
      line "\t.section __DATA,__data"
      line "\t.p2align 3"
      forM_ statics $ \(i, name, fs) -> do
        line ("_kc_" ++ show i ++ ":\t\t\t// static block of " ++ name)
        forM_ fs $ \f -> ins (".quad _kf_" ++ show f)
      line "_keel_heap_ptr:"
      ins ".quad _keel_heap"
      ins (".quad _keel_heap+" ++ show heapSize)
      line ("\t.zerofill __DATA,__bss,_keel_heap," ++ show heapSize ++ ",4")
      line "\t.section __TEXT,__cstring,cstring_literals"
      strs <- gets gsStrings
      forM_ (M.toList strs) $ \(s, l) -> line (l ++ ":\t.asciz " ++ show s)

-- Functions -------------------------------------------------------------------------------

-- | A function with its stack frame: one 8-byte slot per variable.
emitFun :: String -> Fun -> G ()
emitFun lbl (Fun name x base env body) = do
  let vars = nub (x : env ++ bound body)
      slots = M.fromList (zip vars [0 :: Int ..])
      frame = 16 * ((8 * length vars + 15) `div` 16)
  line "\t.p2align 2"
  line (lbl ++ ":\t\t\t// " ++ name)
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  when (frame > 0) $ subSp frame
  forM_ (zip [base ..] env) $ \(j, v) -> do
    ins ("ldr x9, [x0, #" ++ show (8 * j) ++ "]")
    store slots "x9" v
  store slots "x1" x
  expr slots Nothing body

subSp :: Int -> G ()
subSp n
  | n < 4096 = ins ("sub sp, sp, #" ++ show n)
  | otherwise = movImm "x9" (toInteger n) >> ins "sub sp, sp, x9"

epilogue :: G ()
epilogue = ins "mov sp, x29" >> ins "ldp x29, x30, [sp], #16"

-- | Variables bound in a body.
bound :: Expr -> [String]
bound e = case e of
  Ret _ -> []
  Bind x _ rest -> x : bound rest
  BindIf x _ a b rest -> x : bound a ++ bound b ++ bound rest
  BindCase x _ bs rest -> x : concatMap (bound . snd) bs ++ bound rest

type Slots = M.Map String Int

slotOf :: Slots -> String -> String
slotOf slots v = "[sp, #" ++ show (8 * slots M.! v) ++ "]"

store, load' :: Slots -> String -> String -> G ()
store slots r v = ins ("str " ++ r ++ ", " ++ slotOf slots v)
load' slots r v = ins ("ldr " ++ r ++ ", " ++ slotOf slots v)

atom :: Slots -> String -> Atom -> G ()
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

-- | @join@ is Nothing in tail position (return), or the slot and label a branch delivers to.
expr :: Slots -> Maybe (String, String) -> Expr -> G ()
expr slots join e = case e of
  Ret a -> do
    atom slots "x0" a
    case join of
      Nothing -> epilogue >> ins "ret"
      Just (v, lbl) -> store slots "x0" v >> ins ("b " ++ lbl)
  Bind x rhs (Ret (AVar y)) | x == y, Nothing <- join, Just tc <- tailCall rhs -> tc
  Bind x rhs rest -> do
    rhsCode slots rhs
    store slots "x0" x
    expr slots join rest
  BindIf x c a b rest -> do
    let tailPos = isNothingJ && returns x rest
    lElse <- newLabel
    lJoin <- newLabel
    atom slots "x9" c
    ins ("cbz x9, " ++ lElse)
    expr slots (target tailPos x lJoin) a
    line (lElse ++ ":")
    expr slots (target tailPos x lJoin) b
    unless tailPos $ do
      line (lJoin ++ ":")
      expr slots join rest
  BindCase x s bs rest -> do
    let tailPos = isNothingJ && returns x rest
    lJoin <- newLabel
    labels <- mapM (const newLabel) bs
    atom slots "x9" s
    ins "ldr x9, [x9]"
    -- Compare against every tag but the last, which falls through.
    forM_ (zip (init bs) labels) $ \((tag, _), l) -> do
      ins ("cmp x9, #" ++ show tag)
      ins ("b.eq " ++ l)
    ins ("b " ++ last labels)
    forM_ (zip bs labels) $ \((_, body), l) -> do
      line (l ++ ":")
      expr slots (target tailPos x lJoin) body
    unless tailPos $ do
      line (lJoin ++ ":")
      expr slots join rest
  where
    isNothingJ = case join of
      Nothing -> True
      Just _ -> False
    returns x (Ret (AVar y)) = x == y
    returns _ _ = False
    target tailPos x lJoin = if tailPos then Nothing else Just (x, lJoin)

    -- A call in tail position: load the arguments, drop the frame, jump.
    tailCall rhs = case rhs of
      RCall f a -> Just $ do
        atom slots "x0" f
        atom slots "x1" a
        ins "ldr x16, [x0]"
        epilogue
        ins "br x16"
      RCallKnown i a -> Just $ do
        address "x0" ("_kc_" ++ show i)
        atom slots "x1" a
        epilogue
        ins ("b _kf_" ++ show i)
      RProj a i -> Just $ do
        atom slots "x0" a
        ins "mov x1, #0"
        ins ("ldr x16, [x0, #" ++ show (8 * i) ++ "]")
        epilogue
        ins "br x16"
      _ -> Nothing

-- | Allocate @n@ words from the arena into x0 (uses x13–x15).
alloc :: Int -> G ()
alloc n = do
  address "x13" "_keel_heap_ptr"
  ins "ldr x0, [x13]"
  if 8 * n < 4096
    then ins ("add x14, x0, #" ++ show (8 * n))
    else movImm "x14" (toInteger (8 * n)) >> ins "add x14, x0, x14"
  ins "ldr x15, [x13, #8]"
  ins "cmp x14, x15"
  ins "b.hi _keel_panic_oom"
  ins "str x14, [x13]"

-- | Compute a right-hand side into x0.
rhsCode :: Slots -> Rhs -> G ()
rhsCode slots rhs = case rhs of
  RAtom a -> atom slots "x0" a
  RPrim op it a b -> do
    atom slots "x9" a
    atom slots "x10" b
    case op of
      Eq -> ins "cmp x9, x10" >> ins "cset x0, eq"
      Lt -> ins "cmp x9, x10" >> ins ("cset x0, " ++ if signed it then "lt" else "lo")
      Arith ov aop -> arith it ov aop
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
    alloc (1 + length fvs)
    address "x11" ("_kf_" ++ show i)
    ins "str x11, [x0]"
    storeAll 1 fvs
  RCodata is fvs -> do
    alloc (length is + length fvs)
    forM_ (zip [0 :: Int ..] is) $ \(j, i) -> do
      address "x11" ("_kf_" ++ show i)
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
    storeAll (length is) fvs
  RProj a i -> do
    atom slots "x0" a
    ins "mov x1, #0"
    ins ("ldr x16, [x0, #" ++ show (8 * i) ++ "]")
    ins "blr x16"
  RAlloc tag as -> do
    alloc (1 + length as)
    movImm "x11" tag
    ins "str x11, [x0]"
    forM_ (zip [1 :: Int ..] as) $ \(j, a) -> do
      atom slots "x11" a
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
  RField a i -> do
    atom slots "x9" a
    ins ("ldr x0, [x9, #" ++ show (8 * (i + 1)) ++ "]")
  ROut a -> do
    -- Apple ARM64 passes variadic arguments on the stack.
    atom slots "x9" a
    ins "sub sp, sp, #16"
    ins "str x9, [sp]"
    l <- str "%lld\n"
    address "x0" l
    ins "bl _printf"
    ins "add sp, sp, #16"
    ins "mov x0, #0"
  where
    storeAll :: Int -> [String] -> G ()
    storeAll from vs = forM_ (zip [from ..] vs) $ \(j, v) -> do
      load' slots "x11" v
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")

-- | Integer arithmetic (spec §2.5) with x9, x10 as operands and the result in x0. Values are
-- canonical: sign- or zero-extended to 64 bits by their type.
arith :: IntTy -> Overflow -> ArithOp -> G ()
arith it@(IntTy sgn n) ov aop
  | ov == Wrap = do
      plain
      when narrow extend
  | otherwise = do
      lOvf <- if ov == Checked then pure "_keel_panic_overflow" else newLabel
      detect lOvf
      case ov of
        Saturate -> do
          lDone <- newLabel
          ins ("b " ++ lDone)
          line (lOvf ++ ":")
          saturate
          line (lDone ++ ":")
        Optional -> do
          lDone <- newLabel
          ins "mov x12, x0"
          alloc 2
          ins "mov x11, #1" -- Some
          ins "str x11, [x0]"
          ins "str x12, [x0, #8]"
          ins ("b " ++ lDone)
          line (lOvf ++ ":")
          alloc 1
          ins "str xzr, [x0]" -- None
          line (lDone ++ ":")
        _ -> pure ()
  where
    narrow = n < 64
    (lo, hi) = intRange it
    opName = case aop of
      Add -> "add"
      Sub -> "sub"
      Mul -> "mul"
    plain = ins (opName ++ " x0, x9, x10")
    extend
      | sgn = ins ((case n of 8 -> "sxtb"; 16 -> "sxth"; _ -> "sxtw") ++ " x0, w0")
      | otherwise = ins ("and x0, x0, #" ++ show hi)
    -- Branch to lOvf when the exact result doesn't fit.
    detect lOvf
      | narrow && sgn = do
          plain -- exact: narrow operands can't overflow 64 bits
          movImm "x11" lo
          ins "cmp x0, x11"
          ins ("b.lt " ++ lOvf)
          movImm "x11" hi
          ins "cmp x0, x11"
          ins ("b.gt " ++ lOvf)
      | narrow = do
          plain -- unsigned: a negative result is also above hi when compared unsigned
          movImm "x11" hi
          ins "cmp x0, x11"
          ins ("b.hi " ++ lOvf)
      | otherwise = case (aop, sgn) of
          (Add, True) -> ins "adds x0, x9, x10" >> ins ("b.vs " ++ lOvf)
          (Sub, True) -> ins "subs x0, x9, x10" >> ins ("b.vs " ++ lOvf)
          (Mul, True) -> do
            ins "mul x0, x9, x10"
            ins "smulh x11, x9, x10"
            ins "cmp x11, x0, asr #63"
            ins ("b.ne " ++ lOvf)
          (Add, False) -> ins "adds x0, x9, x10" >> ins ("b.cs " ++ lOvf)
          (Sub, False) -> ins "subs x0, x9, x10" >> ins ("b.lo " ++ lOvf)
          (Mul, False) -> do
            ins "mul x0, x9, x10"
            ins "umulh x11, x9, x10"
            ins ("cbnz x11, " ++ lOvf)
    -- The bound in the direction of the overflow.
    saturate
      | narrow && sgn = do
          movImm "x11" lo
          movImm "x12" hi
          ins "cmp x0, x11"
          ins "csel x0, x11, x12, lt"
      | not sgn = if aop == Sub then ins "mov x0, #0" else movImm "x0" hi
      | otherwise = do
          movImm "x11" lo
          movImm "x12" hi
          -- add/sub overflow toward the sign of a; mul toward the sign of a·b
          if aop == Mul then ins "eor x13, x9, x10" >> ins "cmp x13, #0" else ins "cmp x9, #0"
          ins "csel x0, x11, x12, lt"

-- Results ---------------------------------------------------------------------------------

-- | Closed types whose values may need printing, starting from @main@'s type, with labels.
printerTypes :: [Decl] -> Ty -> M.Map String (Ty, String)
printerTypes decls t0 = go M.empty [t0]
  where
    go acc [] = acc
    go acc (t : ts)
      | M.member (prettyTy t) acc || M.size acc >= 500 = go acc ts
      | otherwise = go (M.insert (prettyTy t) (t, "_kp_" ++ show (M.size acc)) acc) (deps t ++ ts)
    deps t = case t of
      TBox a -> [a]
      TPair a b -> [a, b]
      TData d tys | Just (ps, cs) <- dataOf decls d -> concatMap (map (substTy (M.fromList (zip ps tys)) M.empty) . snd) cs
      _ -> []

dataOf :: [Decl] -> String -> Maybe ([String], [(String, [Ty])])
dataOf decls d = case [(ps, cs) | Data _ d' ps cs <- decls, d' == d] of
  r : _ -> Just r
  [] -> Nothing

-- | A printer: value in x0, prints it in the reference evaluator's format (Show Value).
emitPrinter :: [Decl] -> M.Map String (Ty, String) -> String -> Ty -> G ()
emitPrinter decls printers lbl t = do
  line "\t.p2align 2"
  line (lbl ++ ":\t\t\t// print " ++ prettyTy t)
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  ins "sub sp, sp, #32"
  ins "str x0, [sp, #16]" -- the value; [sp] is printf's argument area
  case t of
    TInt (IntTy sgn _) -> do
      ins "str x0, [sp]"
      l <- str (if sgn then "%lld" else "%llu")
      address "x0" l
      ins "bl _printf"
    TBool -> do
      lFalse <- newLabel
      lDone <- newLabel
      ins ("cbz x0, " ++ lFalse)
      printStr "true"
      ins ("b " ++ lDone)
      line (lFalse ++ ":")
      printStr "false"
      line (lDone ++ ":")
    TUnit -> printStr "()"
    TBox a -> printStr "box " >> field Nothing a
    TPair a b -> do
      printStr "("
      field (Just 0) a
      printStr ", "
      field (Just 1) b
      printStr ")"
    TData d tys | Just (ps, cs) <- dataOf decls d -> do
      let inst = substTy (M.fromList (zip ps tys)) M.empty
      lDone <- newLabel
      labels <- mapM (const newLabel) cs
      ins "ldr x9, [sp, #16]"
      ins "ldr x9, [x9]"
      forM_ (zip [0 :: Int ..] labels) $ \(tag, l) -> do
        ins ("cmp x9, #" ++ show tag)
        ins ("b.eq " ++ l)
      forM_ (zip cs labels) $ \((c, fs), l) -> do
        line (l ++ ":")
        printStr c
        unless (null fs) $ do
          printStr "("
          forM_ (zip [0 :: Int ..] fs) $ \(i, ft) -> do
            when (i > 0) $ printStr ", "
            field (Just i) (inst ft)
          printStr ")"
        ins ("b " ++ lDone)
      line (lDone ++ ":")
    TData _ _ -> printStr "<codata>"
    _ -> printStr "<closure>"
  epilogue
  ins "ret"
  where
    -- Print field i of the block (or the value itself) with its type's printer.
    field :: Maybe Int -> Ty -> G ()
    field mi ft = do
      ins "ldr x0, [sp, #16]"
      forM_ mi $ \i -> ins ("ldr x0, [x0, #" ++ show (8 * (i + 1)) ++ "]")
      case M.lookup (prettyTy ft) printers of
        Just (_, l) -> ins ("bl " ++ l)
        Nothing -> printStr "..."

-- | @_main@ runs the Keel main and prints its result as a last line.
emitEntry :: M.Map String (Ty, String) -> Ty -> G ()
emitEntry printers t = do
  line "\t.globl _main"
  line "\t.p2align 2"
  line "_main:"
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  ins "sub sp, sp, #16"
  ins "bl _kf_main"
  ins "str x0, [sp]"
  printStr "result: "
  ins "ldr x0, [sp]"
  forM_ (M.lookup (prettyTy t) printers) $ \(_, l) -> ins ("bl " ++ l)
  printStr "\n"
  ins "mov x0, #0"
  epilogue
  ins "ret"

-- | Panics write a message to stderr and exit with status 101. C @exit@ flushes stdout first,
-- so output written before the panic is kept (spec §2.5).
emitRuntime :: G ()
emitRuntime = do
  panic "_keel_panic_overflow" "panic: arithmetic overflow\n"
  panic "_keel_panic_oom" "panic: out of memory\n"
  where
    panic lbl msg = do
      l <- str msg
      line "\t.p2align 2"
      line (lbl ++ ":")
      ins "mov x0, #2"
      address "x1" l
      ins ("mov x2, #" ++ show (length msg))
      ins "bl _write"
      ins "mov x0, #101"
      ins "bl _exit"
