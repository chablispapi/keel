-- | Code generator: the lowered IR ("Keel.Lower") → Apple ARM64 assembly (Mach-O), assembled
-- and linked with the system @cc@ (notes.md §12, §17).
--
-- Deliberately simple: every variable lives in a stack slot and values pass through scratch
-- registers x9–x17, so nothing needs saving across calls.
-- ponytail: no register allocation (M4); a call in tail position reuses the frame, so loops
-- written as tail recursion run in constant stack.
--
-- Conventions: every function is called with its closure (or codata block) in x0 and its
-- argument in x1, both owned, and returns an owned result in x0. Heap blocks carry a header
-- word at offset -8 (reference count, size, pointer map) and are recycled through free lists
-- (spec/memory.md). Panics exit with status 101 after flushing stdout.
module Keel.AArch64 (compileNative, compileNativeWith, emitProgram, prepare, bound, uses, printerTypes, dataOf, header, heapSize, maxSmall, Loc (..), allocate) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.List (elemIndex, nub, sortOn)
import Data.ByteString qualified as B
import Data.Map.Strict qualified as M
import Data.Maybe (listToMaybe)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Numeric (showOct)
import Keel.Check (checkProgram)
import Keel.Lower
import Keel.Mono (compileWith)
import Keel.Syntax

-- | The whole pipeline: check, elaborate, monomorphize, lower, emit.
compileNative :: Program -> Either String String
compileNative = compileNativeWith False

-- | With @debug@, the assembly carries a line table (.file/.loc) for @cc -g@.
compileNativeWith :: Bool -> Program -> Either String String
compileNativeWith debug p = do
  (decls, t, lp) <- prepareWith debug p
  pure (emitProgram decls t lp)

-- | The target-independent part of every back end: the core pipeline and lowering. Returns
-- the declarations (with built-ins), @main@'s type, and the lowered program.
prepare :: Program -> Either String ([Decl], Ty, LProg)
prepare = prepareWith False

prepareWith :: Bool -> Program -> Either String ([Decl], Ty, LProg)
prepareWith debug p = do
  mono <- either (Left . show) Right (compileWith debug p)
  (t, _) <- either (Left . show) Right (checkProgram mono)
  lp <- lower mono
  let Program decls _ = mono
  pure (optionDecl : decls, t, lp)

heapSize :: Integer
heapSize = 64 * 1024 * 1024

-- | Blocks of up to this many payload words are recycled through free lists.
maxSmall :: Int
maxSmall = 64

-- | gsLocs: the line-table row (file number, line, column) for variables bound by a
-- positioned computation; empty unless the program kept positions (debug builds).
data GS = GS {gsLabel :: Int, gsLines :: [String], gsStrings :: M.Map String String, gsLocs :: M.Map String (Int, Int, Int)}

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
emitProgram decls mainTy (LProg funs statics mainF locs) = unlines (reverse (gsLines (execState gen (GS 0 [] M.empty rows))))
  where
    printers = printerTypes decls mainTy
    files = nub [f | (f, _, _) <- M.elems locs]
    rows = M.map (\(f, l, c) -> (maybe 0 (+ 1) (elemIndex f files), l, c)) locs
    gen = do
      line "\t.section __TEXT,__text,regular,pure_instructions"
      forM_ (zip [1 :: Int ..] files) $ \(n, f) -> ins (".file " ++ show n ++ " " ++ show f)
      forM_ (M.toList funs) $ \(i, f) -> emitFun ("_kf_" ++ show i) f
      emitFun "_kf_main" mainF
      -- The runtime has no Keel source: line 0.
      unless (null files) $ ins ".loc 1 0 0"
      emitEntry printers mainTy
      forM_ (M.toList printers) $ \(_, (t, lbl)) -> emitPrinter decls printers lbl t
      emitRuntime
      line "\t.section __DATA,__data"
      line "\t.p2align 3"
      forM_ statics $ \(i, name, fs) -> do
        ins ".quad 0x80000000\t\t// header: immortal"
        line ("_kc_" ++ show i ++ ":\t\t\t// static block of " ++ name)
        forM_ fs $ \f -> ins (".quad _kf_" ++ show f)
      line "_keel_heap_ptr:"
      ins ".quad _keel_heap"
      ins (".quad _keel_heap+" ++ show heapSize)
      line ("\t.zerofill __DATA,__bss,_keel_heap," ++ show heapSize ++ ",4")
      line ("\t.zerofill __DATA,__bss,_keel_freelists," ++ show (8 * (maxSmall + 1)) ++ ",3")
      line "\t.zerofill __DATA,__bss,_keel_stats,32,3"
      line "\t.zerofill __DATA,__bss,_keel_handlers,8,3"
      line "\t.section __TEXT,__cstring,cstring_literals"
      strs <- gets gsStrings
      forM_ (M.toList strs) $ \(s, l) -> line (l ++ ":\t.asciz " ++ show s)
      case files of
        f : _ -> debugInfo f ([("_kf_" ++ show i, funName fn) | (i, fn) <- M.toList funs] ++ [("_kf_main", "main")])
        [] -> pure ()

-- Functions -------------------------------------------------------------------------------

-- | Register allocation (M4): the most-used variables of a function each get their own
-- callee-saved register for the whole function; the rest live in 8-byte stack slots. Every
-- callee preserves these registers (Keel functions save what they use; the runtime and the C
-- library never touch them), so values survive calls. Returns the locations and the
-- (register, save offset) pairs; the save area follows the slots.
allocate :: [String] -> Fun -> [String] -> (M.Map String Loc, [(String, Int)], Int)
allocate calleeSaved (Fun _ params _ env _ _ body) vars0 =
  (M.fromList ([(v, InReg r) | (v, r) <- inRegs] ++ zip spilled (map InSlot [0 ..])), saved, frame)
  where
    vars = nub vars0
    counts = M.fromListWith (+) [(v, 1 :: Int) | v <- uses body ++ params ++ env]
    inRegs = zip (sortOn (\v -> negate (M.findWithDefault 0 v counts)) vars) calleeSaved
    spilled = [v | v <- vars, v `notElem` map fst inRegs]
    saved = [(r, 8 * (length spilled + i)) | (i, (_, r)) <- zip [0 ..] inRegs]
    frame = 16 * ((8 * (length spilled + length inRegs) + 15) `div` 16)

data Loc = InReg String | InSlot Int

-- | A function's frame: where each variable lives and which registers to restore.
data Slots = Slots {fLocs :: M.Map String Loc, fSaved :: [(String, Int)]}

emitFun :: String -> Fun -> G ()
emitFun lbl f@(Fun name params base env envPtrs dropsSelf body) = do
  when (length params > 7) $ error "more than 7 parameters"
  let (locs, saved, frame) = allocate ["x" ++ show r | r <- [19 .. 28 :: Int]] f (params ++ env ++ bound body)
      slots = Slots locs saved
  line "\t.p2align 2"
  line (lbl ++ ":\t\t\t// " ++ name)
  line ("L" ++ lbl ++ "_begin:")
  -- The prologue belongs to the function's first line, so a breakpoint on it stops there.
  rows <- gets gsLocs
  case [r | v <- bound body, Just r <- [M.lookup v rows]] of
    r : _ -> lineRow r
    [] -> unless (M.null rows) $ ins ".loc 1 0 0"
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  when (frame > 0) $ subSp frame
  forM_ saved $ \(r, off) -> ins ("str " ++ r ++ ", [sp, #" ++ show off ++ "]")
  forM_ (zip [base ..] env) $ \(j, v) -> do
    ins ("ldr x9, [x0, #" ++ show (8 * j) ++ "]")
    store slots "x9" v
  forM_ (zip [1 :: Int ..] params) $ \(r, p) -> store slots ("x" ++ show r) p
  -- Own the captured pointers, then release the block (x0 is still the block: dup uses x16/x17).
  forM_ envPtrs $ \v -> dup slots v
  when dropsSelf $ ins "bl _keel_drop"
  expr slots Nothing body
  line ("L" ++ lbl ++ "_end:")

subSp :: Int -> G ()
subSp n
  | n < 4096 = ins ("sub sp, sp, #" ++ show n)
  | otherwise = movImm "x9" (toInteger n) >> ins "sub sp, sp, x9"

epilogue :: G ()
epilogue = ins "mov sp, x29" >> ins "ldp x29, x30, [sp], #16"

-- | Leave a Keel function: restore its callee-saved registers, then the frame.
leave :: Slots -> G ()
leave slots = do
  forM_ (fSaved slots) $ \(r, off) -> ins ("ldr " ++ r ++ ", [sp, #" ++ show off ++ "]")
  epilogue

-- | Every occurrence of a variable in a body (for ranking variables by use).
uses :: Expr -> [String]
uses e = case e of
  Ret a -> av a
  Bind x rhs rest -> x : rhsVars rhs ++ uses rest
  BindIf x c a b rest -> x : av c ++ uses a ++ uses b ++ uses rest
  BindCase x s bs rest -> x : av s ++ concat [uses b | (_, _, b) <- bs] ++ uses rest
  Dup v rest -> v : uses rest
  Drop v rest -> v : uses rest
  DropReuse v t rest -> v : t : uses rest
  where
    av (AVar v) = [v]
    av _ = []
    rhsVars rhs = case rhs of
      RAtom a -> av a
      RPrim _ _ a b -> av a ++ av b
      RCall f a -> av f ++ av a
      RCallKnown _ as -> concatMap av as
      RClosure _ fvs _ -> fvs
      RCodata _ fvs _ -> fvs
      RProj a _ -> av a
      RAlloc _ _ as -> concatMap av as
      RAllocAt t _ _ as -> t : concatMap av as
      RField a _ -> av a
      RPushHandler cs _ -> concatMap (av . snd) cs
      RPopHandler a -> av a
      RPerform _ a -> av a
      RConv _ a -> av a

-- | Variables bound in a body.
bound :: Expr -> [String]
bound e = case e of
  Ret _ -> []
  Bind x _ rest -> x : bound rest
  BindIf x _ a b rest -> x : bound a ++ bound b ++ bound rest
  BindCase x _ bs rest -> x : concat [bound b | (_, _, b) <- bs] ++ bound rest
  Dup _ rest -> bound rest
  Drop _ rest -> bound rest
  DropReuse _ tok rest -> tok : bound rest

store, load' :: Slots -> String -> String -> G ()
store slots r v = case fLocs slots M.! v of
  InReg x -> unless (x == r) $ ins ("mov " ++ x ++ ", " ++ r)
  InSlot i -> ins ("str " ++ r ++ ", [sp, #" ++ show (8 * i) ++ "]")
load' slots r v = case fLocs slots M.! v of
  InReg x -> unless (x == r) $ ins ("mov " ++ r ++ ", " ++ x)
  InSlot i -> ins ("ldr " ++ r ++ ", [sp, #" ++ show (8 * i) ++ "]")

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

-- | DWARF for debug builds: a compile unit pointing at the line table the assembler builds
-- from the .loc directives, and a subprogram per Keel function, so lldb can break on .kl
-- lines and name functions in backtraces. Paths are absolute (keelc makes them so).
--
-- ponytail: lines and function names only; no variable locations or types, so lldb can't
-- print Keel values yet.
debugInfo :: FilePath -> [(String, String)] -> G ()
debugInfo file fns = do
  line "\t.section __DWARF,__debug_abbrev,regular,debug"
  mapM_ (ins . (".byte " ++) . show)
    ( [1, 0x11, 1, 0x03, 0x08, 0x13, 0x05, 0x10, 0x17, 0x1b, 0x08, 0x11, 0x01, 0x12, 0x06, 0, 0] -- compile unit
        ++ [2, 0x2e, 0, 0x03, 0x08, 0x11, 0x01, 0x12, 0x06, 0, 0] -- subprogram
        ++ [0 :: Int]
    )
  line "\t.section __DWARF,__debug_info,regular,debug"
  line "Ldebug_info:"
  diff "Ldebug_info_end" "Ldebug_info_start"
  line "Ldebug_info_start:"
  ins ".short 4"
  ins ".long 0"
  ins ".byte 8"
  ins ".byte 1"
  cstring file
  -- No DWARF language for Keel; lldb ignores subprograms in assembler units, so say C.
  ins ".short 0x0c"
  diff "Lline_table_start" "Lsection_line"
  cstring "/"
  -- The functions are emitted in this order, main last.
  let first = maybe "_kf_main" fst (listToMaybe fns)
  ins (".quad L" ++ first ++ "_begin")
  diff "L_kf_main_end" ("L" ++ first ++ "_begin")
  forM_ fns $ \(lbl, name) -> do
    ins ".byte 2"
    cstring name
    ins (".quad L" ++ lbl ++ "_begin")
    diff ("L" ++ lbl ++ "_end") ("L" ++ lbl ++ "_begin")
  ins ".byte 0"
  line "Ldebug_info_end:"
  line "\t.section __DWARF,__debug_line,regular,debug"
  line "Lsection_line:"
  line "Lline_table_start:"
  where
    -- A 4-byte difference of local labels, through a .set symbol so the assembler computes it:
    -- written directly, it becomes a relocation pair, which debug sections can't have.
    diff a b = do
      n <- newLabel
      line (n ++ "_set = " ++ a ++ "-" ++ b)
      ins (".long " ++ n ++ "_set")
    -- UTF-8, with octal escapes outside printable ASCII (names like λx).
    cstring s = ins (".asciz \"" ++ concatMap esc (B.unpack (TE.encodeUtf8 (T.pack s))) ++ "\"")
    esc b
      | b >= 32 && b < 127 && b /= 34 && b /= 92 = [toEnum (fromIntegral b)]
      | otherwise = '\\' : pad (showOct b "")
    pad o = replicate (3 - length o) '0' ++ o

-- | A line-table row for the code computing @x@, if it has a position.
loc :: String -> G ()
loc x = gets (M.lookup x . gsLocs) >>= mapM_ lineRow

lineRow :: (Int, Int, Int) -> G ()
lineRow (f, l, c) = ins (".loc " ++ show f ++ " " ++ show l ++ " " ++ show c)

-- | Increment the reference count of a variable's block (inline; uses x16, x17). Immortal
-- blocks (bit 31) are skipped; a count of zero means a freed block, which is a bug.
dup :: Slots -> String -> G ()
dup slots v = do
  lSkip <- newLabel
  load' slots "x16" v
  ins "ldr w17, [x16, #-8]"
  ins ("tbnz w17, #31, " ++ lSkip)
  ins "cbz w17, _keel_panic_rc"
  ins "add w17, w17, #1"
  ins "str w17, [x16, #-8]"
  line (lSkip ++ ":")

-- | @join@ is Nothing in tail position (return), or the slot and label a branch delivers to.
expr :: Slots -> Maybe (String, String) -> Expr -> G ()
expr slots join e = case e of
  Ret a -> do
    atom slots "x0" a
    case join of
      Nothing -> leave slots >> ins "ret"
      Just (v, lbl) -> store slots "x0" v >> ins ("b " ++ lbl)
  Bind x rhs (Ret (AVar y)) | x == y, Nothing <- join, Just tc <- tailCall rhs -> loc x >> tc
  Bind x rhs rest -> do
    loc x
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
    forM_ (zip (init bs) labels) $ \((tag, _, _), l) -> do
      ins ("cmp x9, #" ++ show tag)
      ins ("b.eq " ++ l)
    ins ("b " ++ last labels)
    forM_ (zip bs labels) $ \((_, _, body), l) -> do
      line (l ++ ":")
      expr slots (target tailPos x lJoin) body
    unless tailPos $ do
      line (lJoin ++ ":")
      expr slots join rest
  Dup v rest -> dup slots v >> expr slots join rest
  Drop v rest -> do
    load' slots "x0" v
    ins "bl _keel_drop"
    expr slots join rest
  DropReuse v tok rest -> do
    load' slots "x0" v
    ins "bl _keel_drop_reuse"
    store slots "x0" tok
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
        leave slots
        ins "br x16"
      RCallKnown i as -> Just $ do
        args as
        leave slots
        ins ("b _kf_" ++ show i)
      RProj a i -> Just $ do
        atom slots "x0" a
        ins "mov x1, #0"
        ins ("ldr x16, [x0, #" ++ show (8 * i) ++ "]")
        leave slots
        ins "br x16"
      _ -> Nothing

    args as = forM_ (zip [1 :: Int ..] as) $ \(r, a) -> atom slots ("x" ++ show r) a

-- | Allocate a block of @n@ payload words with a pointer map into x0 (header written).
-- The runtime allocator clobbers only x0, x1 and x13–x16.
alloc :: Int -> Integer -> G ()
alloc n bm = do
  movImm "x0" (toInteger (max 1 n))
  movImm "x1" bm
  ins "bl _keel_alloc"

-- | Header word of a fresh block: count 1, size, pointer map.
header :: Int -> Integer -> Integer
header n bm = 1 .|. (toInteger (max 1 n) `shiftL` 32) .|. (bm `shiftL` 48)

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
      Arith _ aop | aop `elem` [Div, Rem] -> divide it aop
      Arith ov aop -> arith it ov aop
      Bits bop -> bitwise it bop
  RCall f a -> do
    atom slots "x0" f
    atom slots "x1" a
    ins "ldr x16, [x0]"
    ins "blr x16"
  RCallKnown i as -> do
    forM_ (zip [1 :: Int ..] as) $ \(r, a) -> atom slots ("x" ++ show r) a
    ins ("bl _kf_" ++ show i)
  RClosure i fvs bm -> do
    alloc (1 + length fvs) bm
    address "x11" ("_kf_" ++ show i)
    ins "str x11, [x0]"
    storeAll 1 fvs
  RCodata is fvs bm -> do
    alloc (length is + length fvs) bm
    forM_ (zip [0 :: Int ..] is) $ \(j, i) -> do
      address "x11" ("_kf_" ++ show i)
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
    storeAll (length is) fvs
  RProj a i -> do
    atom slots "x0" a
    ins "mov x1, #0"
    ins ("ldr x16, [x0, #" ++ show (8 * i) ++ "]")
    ins "blr x16"
  RAlloc tag bm as -> do
    alloc (1 + length as) bm
    fields tag as
  RAllocAt tok tag bm as -> do
    -- In place if the token holds a block (it was unique); otherwise allocate.
    lFresh <- newLabel
    lDone <- newLabel
    load' slots "x0" tok
    ins ("cbz x0, " ++ lFresh)
    movImm "x15" (header (1 + length as) bm)
    ins "str x15, [x0, #-8]"
    address "x13" "_keel_stats"
    ins "ldr x14, [x13, #16]"
    ins "add x14, x14, #1"
    ins "str x14, [x13, #16]"
    ins ("b " ++ lDone)
    line (lFresh ++ ":")
    alloc (1 + length as) bm
    line (lDone ++ ":")
    fields tag as
  RField a i -> do
    atom slots "x9" a
    ins ("ldr x0, [x9, #" ++ show (8 * (i + 1)) ++ "]")
  RPushHandler cs bm -> do
    alloc (2 + 2 * length cs) bm
    address "x12" "_keel_handlers"
    ins "ldr x11, [x12]"
    ins "str x11, [x0]" -- the enclosing frame
    movImm "x11" (toInteger (length cs))
    ins "str x11, [x0, #8]"
    forM_ (zip [0 :: Int ..] cs) $ \(i, (n, a)) -> do
      movImm "x11" (toInteger n)
      ins ("str x11, [x0, #" ++ show (8 * (2 + 2 * i)) ++ "]")
      atom slots "x11" a
      ins ("str x11, [x0, #" ++ show (8 * (3 + 2 * i)) ++ "]")
    ins "str x0, [x12]"
  RPopHandler a -> do
    atom slots "x0" a
    ins "ldr x9, [x0]"
    address "x10" "_keel_handlers"
    ins "str x9, [x10]"
    ins "bl _keel_drop"
    ins "mov x0, #0"
  RConv to a -> do
    -- Canonical values already have the right 64-bit pattern; narrow targets re-extend.
    atom slots "x0" a
    canonical to
  RPerform n a -> do
    atom slots "x1" a
    movImm "x0" (toInteger n)
    ins "bl _keel_perform"
  where
    storeAll :: Int -> [String] -> G ()
    storeAll from vs = forM_ (zip [from ..] vs) $ \(j, v) -> do
      load' slots "x11" v
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
    fields :: Integer -> [Atom] -> G ()
    fields tag as = do
      movImm "x11" tag
      ins "str x11, [x0]"
      forM_ (zip [1 :: Int ..] as) $ \(j, a) -> do
        atom slots "x11" a
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
          ins "mov x12, x0" -- the allocator leaves x9–x12 alone
          alloc 2 0
          ins "mov x11, #1" -- Some
          ins "str x11, [x0]"
          ins "str x12, [x0, #8]"
          ins ("b " ++ lDone)
          line (lOvf ++ ":")
          alloc 1 0
          ins "str xzr, [x0]" -- None
          line (lDone ++ ":")
        _ -> pure ()
  where
    narrow = n < 64
    (lo, hi) = intRange it
    opName = case aop of
      Add -> "add"
      Sub -> "sub"
      _ -> "mul"
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
          (_, True) -> do -- Mul (division never reaches here: see divide)
            ins "mul x0, x9, x10"
            ins "smulh x11, x9, x10"
            ins "cmp x11, x0, asr #63"
            ins ("b.ne " ++ lOvf)
          (Add, False) -> ins "adds x0, x9, x10" >> ins ("b.cs " ++ lOvf)
          (Sub, False) -> ins "subs x0, x9, x10" >> ins ("b.lo " ++ lOvf)
          (_, False) -> do -- Mul
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

-- | Checked division with x9, x10 as operands and the result in x0. Canonical values divide
-- exactly in 64 bits; the only overflow is min / -1, caught by a range check for narrow types
-- and explicitly for i64 (the hardware returns min without trapping).
divide :: IntTy -> ArithOp -> G ()
divide it@(IntTy sgn n) aop = do
  ins "cbz x10, _keel_panic_div"
  when (sgn && n == 64 && aop == Div) $ do
    lOk <- newLabel
    ins "cmn x10, #1"
    ins ("b.ne " ++ lOk)
    movImm "x11" (fst (intRange it))
    ins "cmp x9, x11"
    ins "b.eq _keel_panic_overflow"
    line (lOk ++ ":")
  let d = if sgn then "sdiv" else "udiv"
  case aop of
    Div -> ins (d ++ " x0, x9, x10")
    _ -> ins (d ++ " x11, x9, x10") >> ins "msub x0, x11, x10, x9"
  when (sgn && n < 64 && aop == Div) $ do
    movImm "x11" (snd (intRange it))
    ins "cmp x0, x11"
    ins "b.gt _keel_panic_overflow"

-- | Re-extend x0 to the canonical form of an integer type (no-op for 64-bit types).
canonical :: IntTy -> G ()
canonical it@(IntTy sgn n)
  | n == 64 = pure ()
  | sgn = ins ((case n of 8 -> "sxtb"; 16 -> "sxth"; _ -> "sxtw") ++ " x0, w0")
  | otherwise = ins ("and x0, x0, #" ++ show (snd (intRange it)))

-- | Bitwise operations with x9, x10 as operands and the result in x0, matching the evaluator:
-- a shift by a negative amount is a shift by 0, and by 64 or more shifts everything out.
bitwise :: IntTy -> BitOp -> G ()
bitwise it@(IntTy sgn n) bop = case bop of
  And -> ins "and x0, x9, x10"
  Or -> ins "orr x0, x9, x10"
  Xor -> ins "eor x0, x9, x10"
  Shl -> shift "lsl" >> when (n < 64) extend
  Shr -> shift (if sgn then "asr" else "lsr")
  where
    (_, hi) = intRange it
    extend
      | sgn = ins ((case n of 8 -> "sxtb"; 16 -> "sxth"; _ -> "sxtw") ++ " x0, w0")
      | otherwise = ins ("and x0, x0, #" ++ show hi)
    shift instr = do
      lBig <- newLabel
      lDone <- newLabel
      when sgn $ ins "cmp x10, #0" >> ins "csel x10, xzr, x10, lt"
      ins "cmp x10, #63"
      ins ("b.hi " ++ lBig)
      ins (instr ++ " x0, x9, x10")
      ins ("b " ++ lDone)
      line (lBig ++ ":")
      if instr == "asr" then ins "asr x0, x9, #63" else ins "mov x0, #0"
      line (lDone ++ ":")

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

-- | A printer: value in x0 (borrowed), prints it in the reference evaluator's format.
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

-- | @_main@ runs the Keel main, prints its result as a last line, drops it, and with
-- KEEL_STATS set reports the allocator counters on stderr.
emitEntry :: M.Map String (Ty, String) -> Ty -> G ()
emitEntry printers t = do
  line "\t.globl _main"
  line "\t.p2align 2"
  line "_main:"
  ins "stp x29, x30, [sp, #-16]!"
  ins "mov x29, sp"
  ins "sub sp, sp, #64"
  ins "mov x0, #0"
  ins "bl _kf_main"
  ins "str x0, [sp, #48]"
  printStr "result: "
  ins "ldr x0, [sp, #48]"
  forM_ (M.lookup (prettyTy t) printers) $ \(_, l) -> ins ("bl " ++ l)
  printStr "\n"
  when (isPtr t) $ ins "ldr x0, [sp, #48]" >> ins "bl _keel_drop"
  lNoStats <- newLabel
  name <- str "KEEL_STATS"
  address "x0" name
  ins "bl _getenv"
  ins ("cbz x0, " ++ lNoStats)
  -- dprintf(2, fmt, allocs, recycled, in-place, freed, live): variadic arguments on the stack
  address "x13" "_keel_stats"
  ins "ldp x9, x10, [x13]"
  ins "ldp x11, x12, [x13, #16]"
  ins "stp x9, x10, [sp]"
  ins "stp x11, x12, [sp, #16]"
  ins "add x14, x9, x10"
  ins "add x14, x14, x11"
  ins "sub x14, x14, x12"
  ins "str x14, [sp, #32]"
  fmt <- str "keel-stats: allocs=%lld recycled=%lld inplace=%lld freed=%lld live=%lld\n"
  ins "mov x0, #2"
  address "x1" fmt
  ins "bl _dprintf"
  line (lNoStats ++ ":")
  ins "mov x0, #0"
  epilogue
  ins "ret"

-- Runtime ---------------------------------------------------------------------------------

-- | Allocation, reference counting and panics. Header word: bits 0–31 reference count (bit 31
-- marks an immortal static block, 0 a freed one), 32–47 payload size in words, 48–63 pointer
-- map. Statistics at @_keel_stats@: fresh allocations, recycled, in place, freed.
emitRuntime :: G ()
emitRuntime = do
  -- _keel_alloc: x0 = payload words, x1 = pointer map → x0 = payload. Clobbers x13–x16 only.
  fn "_keel_alloc"
  ins ("cmp x0, #" ++ show maxSmall)
  ins "b.hi L_alloc_bump"
  address "x13" "_keel_freelists"
  ins "ldr x14, [x13, x0, lsl #3]"
  ins "cbz x14, L_alloc_bump"
  ins "ldr x15, [x14]" -- next free block
  ins "str x15, [x13, x0, lsl #3]"
  stat 8 "x15" "x16"
  ins "b L_alloc_header"
  line "L_alloc_bump:"
  address "x13" "_keel_heap_ptr"
  ins "ldr x14, [x13]"
  ins "add x15, x14, x0, lsl #3"
  ins "add x15, x15, #8"
  ins "ldr x16, [x13, #8]"
  ins "cmp x15, x16"
  ins "b.hi _keel_panic_oom"
  ins "str x15, [x13]"
  ins "add x14, x14, #8"
  stat 0 "x15" "x16"
  line "L_alloc_header:"
  ins "lsl x15, x0, #32"
  ins "orr x15, x15, x1, lsl #48"
  ins "orr x15, x15, #1"
  ins "str x15, [x14, #-8]"
  ins "mov x0, x14"
  ins "ret"

  -- _keel_drop: x0 = block. Decrement; at zero, drop the children and free the block. The last
  -- pointer child is handled by looping, so dropping a long list uses constant stack.
  fn "_keel_drop"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  line "L_drop_top:"
  ins "ldr w9, [x0, #-8]"
  ins "tbnz w9, #31, L_drop_ret"
  ins "cbz w9, _keel_panic_rc"
  ins "sub w9, w9, #1"
  ins "str w9, [x0, #-8]"
  ins "cbnz w9, L_drop_ret"
  stat 24 "x12" "x13"
  ins "str x0, [sp, #16]"
  ins "ldr x11, [x0, #-8]"
  ins "lsr x11, x11, #48"
  line "L_drop_loop:"
  ins "cbz x11, L_drop_free"
  ins "sub x13, x11, #1"
  ins "tst x11, x13"
  ins "b.eq L_drop_last" -- one pointer child left
  ins "rbit x13, x11"
  ins "clz x13, x13"
  ins "mov x14, #1"
  ins "lsl x14, x14, x13"
  ins "bic x11, x11, x14"
  ins "str x11, [sp, #24]"
  ins "ldr x9, [sp, #16]"
  ins "ldr x0, [x9, x13, lsl #3]"
  ins "bl _keel_drop"
  ins "ldr x11, [sp, #24]"
  ins "b L_drop_loop"
  line "L_drop_last:"
  ins "rbit x13, x11"
  ins "clz x13, x13"
  ins "ldr x0, [sp, #16]"
  ins "ldr x9, [x0, x13, lsl #3]"
  ins "str x9, [sp, #24]"
  ins "bl _keel_free_block"
  ins "ldr x0, [sp, #24]"
  ins "b L_drop_top"
  line "L_drop_free:"
  ins "ldr x0, [sp, #16]"
  ins "bl _keel_free_block"
  line "L_drop_ret:"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  -- _keel_free_block: x0 = block with count 0 → push it on its size's free list.
  fn "_keel_free_block"
  ins "ldr x10, [x0, #-8]"
  ins "ubfx x11, x10, #32, #16"
  ins ("cmp x11, #" ++ show maxSmall)
  ins "b.hi L_free_ret" -- ponytail: large blocks are not recycled
  address "x12" "_keel_freelists"
  ins "ldr x13, [x12, x11, lsl #3]"
  ins "str x13, [x0]"
  ins "str x0, [x12, x11, lsl #3]"
  line "L_free_ret:"
  ins "ret"

  -- _keel_drop_reuse: x0 = block → x0 = the block, if it was unique (its children dropped,
  -- count 0 until reused), or 0 after an ordinary decrement.
  fn "_keel_drop_reuse"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  ins "ldr w9, [x0, #-8]"
  ins "tbnz w9, #31, L_reuse_none"
  ins "cbz w9, _keel_panic_rc"
  ins "cmp w9, #1"
  ins "b.ne L_reuse_shared"
  stat 24 "x12" "x13"
  ins "str x0, [sp, #16]"
  ins "ldr x11, [x0, #-8]"
  ins "lsr x11, x11, #48"
  line "L_reuse_loop:"
  ins "cbz x11, L_reuse_done"
  ins "rbit x13, x11"
  ins "clz x13, x13"
  ins "mov x14, #1"
  ins "lsl x14, x14, x13"
  ins "bic x11, x11, x14"
  ins "str x11, [sp, #24]"
  ins "ldr x9, [sp, #16]"
  ins "ldr x0, [x9, x13, lsl #3]"
  ins "bl _keel_drop"
  ins "ldr x11, [sp, #24]"
  ins "b L_reuse_loop"
  line "L_reuse_done:"
  ins "ldr x0, [sp, #16]"
  ins "str wzr, [x0, #-8]"
  ins "b L_reuse_ret"
  line "L_reuse_shared:"
  ins "sub w9, w9, #1"
  ins "str w9, [x0, #-8]"
  line "L_reuse_none:"
  ins "mov x0, #0"
  line "L_reuse_ret:"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  -- _keel_perform: x0 = operation number, x1 = argument (owned) → x0 = result. Finds the
  -- innermost frame handling the operation and calls its clause with the frames outside it
  -- installed; unhandled operations go to the machine.
  fn "_keel_perform"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  address "x9" "_keel_handlers"
  ins "ldr x10, [x9]"
  ins "str x10, [sp, #16]" -- restored afterwards
  line "L_perform_frame:"
  ins "cbz x10, L_perform_machine"
  ins "ldr x11, [x10, #8]" -- clauses in this frame
  ins "add x12, x10, #16"
  line "L_perform_scan:"
  ins "cbz x11, L_perform_next"
  ins "ldr x13, [x12]"
  ins "cmp x13, x0"
  ins "b.eq L_perform_found"
  ins "add x12, x12, #16"
  ins "sub x11, x11, #1"
  ins "b L_perform_scan"
  line "L_perform_next:"
  ins "ldr x10, [x10]"
  ins "b L_perform_frame"
  line "L_perform_found:"
  ins "ldr x14, [x10]"
  ins "str x14, [x9]" -- the clause runs under the enclosing frames
  ins "ldr x0, [x12, #8]"
  -- the call consumes the closure, but the frame keeps it: duplicate first
  ins "ldr w15, [x0, #-8]"
  ins "tbnz w15, #31, L_perform_call"
  ins "add w15, w15, #1"
  ins "str w15, [x0, #-8]"
  line "L_perform_call:"
  ins "ldr x16, [x0]"
  ins "blr x16"
  ins "ldr x10, [sp, #16]"
  address "x9" "_keel_handlers"
  ins "str x10, [x9]"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"
  line "L_perform_machine:"
  ins "cmp x0, #1" -- putc
  ins "b.eq L_perform_putc"
  ins "cbnz x0, _keel_panic_unhandled" -- operation 0 is out; MMIO needs a freestanding target
  ins "sub sp, sp, #16"
  ins "str x1, [sp]" -- printf's variadic argument
  fmt <- str "%lld\n"
  address "x0" fmt
  ins "bl _printf"
  ins "add sp, sp, #16"
  ins "mov x0, #0"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"
  line "L_perform_putc:"
  ins "mov x0, x1"
  ins "bl _putchar"
  ins "mov x0, #0"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  panic "_keel_panic_unhandled" "panic: unhandled operation (MMIO needs a freestanding target)\n"
  panic "_keel_panic_div" "panic: division by zero\n"
  panic "_keel_panic_overflow" "panic: arithmetic overflow\n"
  panic "_keel_panic_oom" "panic: out of memory\n"
  panic "_keel_panic_rc" "panic: reference count error\n"
  where
    fn lbl = line "\t.p2align 2" >> line (lbl ++ ":")
    -- Increment the statistics counter at this byte offset, using two free scratch registers.
    stat :: Int -> String -> String -> G ()
    stat off r1 r2 = do
      address r1 "_keel_stats"
      ins ("ldr " ++ r2 ++ ", [" ++ r1 ++ ", #" ++ show off ++ "]")
      ins ("add " ++ r2 ++ ", " ++ r2 ++ ", #1")
      ins ("str " ++ r2 ++ ", [" ++ r1 ++ ", #" ++ show off ++ "]")
    panic lbl msg = do
      l <- str msg
      fn lbl
      ins "mov x0, #2"
      address "x1" l
      ins ("mov x2, #" ++ show (length msg))
      ins "bl _write"
      ins "mov x0, #101"
      ins "bl _exit"
