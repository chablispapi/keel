-- | RISC-V back end (M3): the lowered IR ("Keel.Lower") → RV64IM or RV32IM assembly for a
-- freestanding target, QEMU's @virt@ board (notes.md §12, §15). Same structure and conventions
-- as "Keel.AArch64"; only the instructions and the runtime differ.
--
-- RV32 (@compileRiscVAt 32@) is the same code with 4-byte words: a block's fields, closures'
-- captured values, handler frames and array elements are 4 bytes each. A block keeps its 8-byte
-- header, so the runtime reads headers as on RV64; stack slots, the free-list table and the
-- runtime's own variables stay 8 bytes apart and use their low word. 'ins' turns the 64-bit
-- instructions into their RV32 ones. A 64-bit integer (i64, u64) isn't supported there yet.
--
-- Freestanding: no operating system and no C library. The runtime prints through the board's
-- 16550 UART (0x1000_0000), exits through its test device (0x10_0000), and performs unhandled
-- MMIO operations as real memory accesses and Hart operations as csrr, csrs and wfi. The program is linked at 0x8000_0000 (see
-- 'linkerScript') and run with @qemu-system-riscv64 -machine virt -bios none -kernel prog.elf@.
--
-- Registers: a0 = block / result, a1 = argument; t0–t3 operands and temporaries (the allocator
-- leaves them alone; t3 also addresses stack slots beyond 2 KB); a6/a7 for inline reference
-- counting; s0 frame pointer.
module Keel.RiscV (Board (..), boardXlen, compileRiscV, compileRiscVAt, compileRiscVFor, linkerScript) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.AArch64 (Loc (..), constData, allocate, bound, dataOf, header, heapSize, keyOf, maxSmall, prepareAt, printerTypes, pruneRuntime, runtimeBegin, runtimeEnd, template)
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Keel.Lower
import Keel.Syntax

-- | What the image runs on: QEMU's virt board as RV64 or RV32 (the register width in bits), or
-- the Raspberry Pi Pico 2's RISC-V cores (RP2350, RV32; notes.md §18).
data Board = Virt Int | Pico2
  deriving (Eq)

boardXlen :: Board -> Int
boardXlen b = case b of
  Virt n -> n
  Pico2 -> 32

compileRiscV :: Program -> Either String String
compileRiscV = compileRiscVAt 64

-- | For QEMU's virt board as RV64 or RV32 (the register width in bits).
compileRiscVAt :: Int -> Program -> Either String String
compileRiscVAt = compileRiscVFor . Virt

compileRiscVFor :: Board -> Program -> Either String String
compileRiscVFor board p = do
  let xlen = boardXlen board
  (decls, t, lp) <- prepareAt xlen False p
  -- ponytail: register pairs for i64 and u64 on RV32 come next.
  let wide = not (S.null (lWide lp)) || t `elem` [TInt (IntTy sgn 64) | sgn <- [False, True]]
        || or [n < -(2 ^ (31 :: Int)) || n >= 2 ^ (32 :: Int) | (_, h, as) <- lConsts lp, AInt n <- maybe [] pure h ++ as]
  when (xlen == 32 && wide) $
    Left "not supported yet on riscv32: 64-bit integers (i64, u64); use i32, u32 or usize"
  emitProgram board decls t lp

-- | The heap's and the stack's sizes in bytes. The Pico 2 has 520 KB of SRAM, which also holds
-- the runtime's variables.
heapBytes, stackBytes :: Board -> Integer
heapBytes b = if b == Pico2 then 384 * 1024 else heapSize
stackBytes b = if b == Pico2 then 64 * 1024 else 8 * 1024 * 1024

-- | QEMU's virt board: link at the start of its RAM, where QEMU loads the kernel image. The
-- Pico 2: code and constants in flash, from 0x1000_0000, where the boot ROM looks for the
-- image; the variables in SRAM, copied there from flash at startup ('emitStart').
linkerScript :: Board -> String
linkerScript b = unlines $ case b of
  Virt _ ->
    [ "OUTPUT_ARCH(riscv)"
    , "ENTRY(_start)"
    , "SECTIONS {"
    , "  . = 0x80000000;"
    , "  .text : { *(.text.start) *(.text*) }"
    , "  .rodata : { *(.rodata*) }"
    , "  .data : { *(.data*) }"
    , "  .bss : { *(.bss*) *(COMMON) }"
    , "}"
    ]
  Pico2 ->
    [ "OUTPUT_ARCH(riscv)"
    , "ENTRY(_start)"
    , "MEMORY {"
    , "  FLASH (rx) : ORIGIN = 0x10000000, LENGTH = 4M"
    , "  RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 520K"
    , "}"
    , "SECTIONS {"
    , "  .text : { *(.text.start) *(.text*) } > FLASH"
    , "  .rodata : { *(.rodata*) } > FLASH"
    , "  .data : { _keel_data = .; *(.data*) . = ALIGN(4); _keel_data_end = .; } > RAM AT > FLASH"
    , "  _keel_data_load = LOADADDR(.data);"
    , "  .bss (NOLOAD) : { *(.bss*) *(COMMON) } > RAM"
    , "}"
    ]

-- | gsWord: the word's size in bytes, 8 (RV64) or 4 (RV32).
data GS = GS {gsLabel :: Int, gsLines :: [String], gsStrings :: M.Map String String, gsNullary :: S.Set Integer, gsLayouts :: M.Map (Integer, Int, Integer) Integer, gsWord :: Int, gsBoard :: Board}

type G = State GS

line :: String -> G ()
line l = modify (\s -> s {gsLines = l : gsLines s})

-- | An instruction, written for RV64. On RV32 a 64-bit load or store becomes a word one, and a
-- W instruction (32 bits, sign-extended) the plain one: the registers are 32 bits wide.
ins :: String -> G ()
ins i = do
  w <- gets gsWord
  let (op, rest) = break (== ' ') i
      op' = if w == 8 then op else M.findWithDefault op op rv32
  line ("\t" ++ op' ++ rest)
  where
    rv32 = M.fromList [("ld", "lw"), ("sd", "sw"), ("lwu", "lw"), ("addiw", "addi"), ("srliw", "srli")]

-- | The word's size in bytes, and log₂ of it.
wordSize, wordShift :: G Int
wordSize = gets gsWord
wordShift = (\w -> if w == 8 then 3 else 2) <$> wordSize

-- | The register width in bits.
xlenBits :: G Int
xlenBits = (* 8) <$> wordSize

newLabel :: G String
newLabel = do
  n <- gets gsLabel
  modify (\s -> s {gsLabel = n + 1})
  pure (".Lk" ++ show n)


str :: String -> G String
str s = do
  m <- gets gsStrings
  case M.lookup s m of
    Just l -> pure l
    Nothing -> do
      let l = "_keel_s" ++ show (M.size m)
      modify (\st -> st {gsStrings = M.insert s l m})
      pure l

printStr :: String -> G ()
printStr s = do
  l <- str s
  ins ("la a0, " ++ l)
  ins "call _keel_print_str"

-- | Load a constant (any pattern of the register's width, given as a mathematical integer).
li :: String -> Integer -> G ()
li r n = do
  bitsN <- xlenBits
  let u = n `mod` (2 ^ bitsN)
  ins ("li " ++ r ++ ", " ++ show (if u >= 2 ^ (bitsN - 1) then u - 2 ^ bitsN else u))

-- | A pointer-sized word in the data section, at an 8-byte spacing on both widths (the
-- runtime's variables are 8 bytes apart; on RV32 it uses their low word).
dataPtr :: Int -> String -> [String]
dataPtr w v = if w == 8 then ["\t.dword " ++ v] else ["\t.word " ++ v, "\t.word 0"]

-- | Write a header (a 64-bit pattern) to -8(r). Clobbers t6.
storeHeader :: String -> Integer -> G ()
storeHeader r h = do
  w <- wordSize
  if w == 8
    then li "t6" h >> ins ("sd t6, -8(" ++ r ++ ")")
    else do
      li "t6" (h .&. 0xffffffff) >> ins ("sw t6, -8(" ++ r ++ ")")
      li "t6" (h `shiftR` 32) >> ins ("sw t6, -4(" ++ r ++ ")")

-- | The pointer map of the block in @r@ (bits 40–55 of its header, with the packed bit 56) into
-- @d@.
headerMap :: String -> String -> G ()
headerMap d r = do
  w <- wordSize
  if w == 8
    then ins ("ld " ++ d ++ ", -8(" ++ r ++ ")") >> ins ("slli " ++ d ++ ", " ++ d ++ ", 7") >> ins ("srli " ++ d ++ ", " ++ d ++ ", 47")
    else ins ("lw " ++ d ++ ", -4(" ++ r ++ ")") >> ins ("slli " ++ d ++ ", " ++ d ++ ", 7") >> ins ("srli " ++ d ++ ", " ++ d ++ ", 15")

-- | Jump to a possibly distant label when a condition holds. Conditional branches only reach
-- ±4 KiB, so branch over an unconditional jump instead.
jumpIf :: String -> [String] -> String -> G ()
jumpIf cond operands target = do
  lSkip <- newLabel
  ins (inverse cond ++ " " ++ concatMap (++ ", ") operands ++ lSkip)
  ins ("j " ++ target)
  line (lSkip ++ ":")
  where
    inverse c = case c of
      "beq" -> "bne"
      "bne" -> "beq"
      "blt" -> "bge"
      "bge" -> "blt"
      "bltu" -> "bgeu"
      "bgeu" -> "bltu"
      "bgt" -> "ble"
      "ble" -> "bgt"
      "bgtu" -> "bleu"
      "bleu" -> "bgtu"
      "beqz" -> "bnez"
      "bnez" -> "beqz"
      "bltz" -> "bgez"
      "bgez" -> "bltz"
      _ -> error ("jumpIf: " ++ c)

emitProgram :: Board -> [Decl] -> Ty -> LProg -> Either String String
emitProgram board decls mainTy (LProg funs statics mainF _ layouts consts _) = Right (unlines (pruneRuntime (reverse (gsLines final))))
  where
    w = boardXlen board `div` 8
    final = execState gen (GS 0 [] M.empty S.empty layouts w board)
    printers = printerTypes decls mainTy
    gen = do
      line "\t.section .text.start, \"ax\""
      if board == Pico2 then emitBoot else emitStart printers mainTy
      line "\t.text"
      forM_ (M.toList funs) $ \(i, f) -> emitFun ("_kf_" ++ show i) f
      emitFun "_kf_main" mainF
      forM_ (M.toList printers) $ \(_, (t, lbl)) -> emitPrinter decls printers lbl t
      line runtimeBegin
      emitRuntime
      line runtimeEnd
      line "\t.data"
      line "\t.p2align 3"
      forM_ statics $ \(i, name, fs) -> do
        ins ".dword 0x80000000\t\t# header: immortal"
        line ("_kc_" ++ show i ++ ":\t\t\t# static block of " ++ name)
        forM_ fs $ \f -> ins ((if w == 8 then ".dword" else ".word") ++ " _kf_" ++ show f)
      tags <- gets gsNullary
      forM_ (S.toList tags) $ \t -> do
        ins (".dword " ++ show (header layouts t .|. 0x80000000) ++ "\t\t# header: immortal, layout " ++ show t)
        line ("_kn_" ++ show t ++ ":\t\t\t# every constructor without fields with this layout")
      mapM_ line (constData (".dword", if w == 8 then ".dword" else ".word", ".word", ".L") layouts consts)
      -- The words and pointer map of each layout whose header holds a field, as in "Keel.AArch64".
      line "\t.p2align 2"
      line "_keel_layouts:"
      let byId = M.fromList [(i, (n, bm)) | ((_, n, bm), i) <- M.toList layouts]
      forM_ [fieldLayouts .. maybe (fieldLayouts - 1) fst (M.lookupMax byId)] $ \i ->
        ins (".word " ++ show (maybe 0 (\(n, bm) -> toInteger n .|. (bm `shiftL` 8)) (M.lookup i byId)))
      line "\t.p2align 3"
      line "_keel_heap_ptr:"
      mapM_ line (dataPtr w "_keel_heap" ++ dataPtr w ("_keel_heap+" ++ show (heapBytes board)))
      line "_keel_arena_base:" -- as in "Keel.AArch64"
      ins ".dword -1"
      line "_keel_arena_top:"
      ins ".dword 0"
      line "_keel_fl:"
      mapM_ line (dataPtr w "_keel_freelists")
      -- Zero-initialized state lives in .data so it needs no clearing at startup.
      line "_keel_freelists:"
      ins (".zero " ++ show (8 * (maxSmall + 1)))
      line "_keel_nofree:"
      ins (".zero " ++ show (8 * (maxSmall + 1)))
      line "_keel_stats:"
      ins ".zero 32"
      line "_keel_handlers:"
      ins ".zero 8"
      line "\t.bss"
      line "\t.p2align 4"
      line "_keel_heap:"
      ins (".zero " ++ show (heapBytes board))
      line "_keel_stack:"
      ins (".zero " ++ show (stackBytes board))
      line "_keel_stack_top:"
      line "\t.section .rodata"
      strs <- gets gsStrings
      forM_ (M.toList strs) $ \(s, l) -> line (l ++ ":\t.asciz " ++ show s)

-- Functions -------------------------------------------------------------------------------

-- | A function's frame: where each variable lives and which registers to restore
-- (register allocation as in "Keel.AArch64", with s1–s11).
-- fLoop: the function's own label, when a call to itself in tail position can jump back to
-- where the arguments are stored instead of leaving and re-entering the frame.
data Slots = Slots {fLocs :: M.Map String Loc, fSaved :: [(String, Int)], fLoop :: Maybe String}

emitFun :: String -> Fun -> G ()
emitFun lbl f@(Fun name params base env envPtrs dropsSelf body) = do
  let (locs, saved, frame) = allocate ["s" ++ show r | r <- [1 .. 11 :: Int]] f (params ++ env ++ bound body)
      slots = Slots locs saved (if null env && not dropsSelf then Just lbl else Nothing)
  line "\t.p2align 2"
  line (lbl ++ ":\t\t\t# " ++ name)
  ins "addi sp, sp, -16"
  ins "sd ra, 8(sp)"
  ins "sd s0, 0(sp)"
  ins "mv s0, sp"
  when (frame > 0) $ if frame <= 2048 then ins ("addi sp, sp, -" ++ show frame) else li "t3" (toInteger frame) >> ins "sub sp, sp, t3"
  forM_ saved $ \(r, off) -> slot off >>= \s -> ins ("sd " ++ r ++ ", " ++ s)
  w <- wordSize
  forM_ (zip [base ..] env) $ \(j, v) -> do
    ins ("ld t0, " ++ show (w * j) ++ "(a0)")
    store slots "t0" v
  line ("L" ++ lbl ++ "_loop:")
  forM_ (zip [1 :: Int ..] params) $ \(r, p) -> store slots ("a" ++ show r) p
  forM_ envPtrs $ \v -> dup slots v
  when dropsSelf $ ins "call _keel_drop"
  expr slots Nothing body

-- | Leave a Keel function: restore its callee-saved registers, then the frame.
leave :: Slots -> G ()
leave slots = do
  forM_ (fSaved slots) $ \(r, off) -> slot off >>= \s -> ins ("ld " ++ r ++ ", " ++ s)
  epilogue

-- | A frame offset as an address: off(sp), or through t3 past the 12-bit offset range.
slot :: Int -> G String
slot off
  | off < 2048 = pure (show off ++ "(sp)")
  | otherwise = li "t3" (toInteger off) >> ins "add t3, t3, sp" >> pure "0(t3)"

epilogue :: G ()
epilogue = do
  ins "mv sp, s0"
  ins "ld ra, 8(sp)"
  ins "ld s0, 0(sp)"
  ins "addi sp, sp, 16"

store, load' :: Slots -> String -> String -> G ()
store slots r v = case fLocs slots M.! v of
  InReg x -> unless (x == r) $ ins ("mv " ++ x ++ ", " ++ r)
  InSlot i -> slot (8 * i) >>= \s -> ins ("sd " ++ r ++ ", " ++ s)
load' slots r v = case fLocs slots M.! v of
  InReg x -> unless (x == r) $ ins ("mv " ++ r ++ ", " ++ x)
  InSlot i -> slot (8 * i) >>= \s -> ins ("ld " ++ r ++ ", " ++ s)

atom :: Slots -> String -> Atom -> G ()
atom slots r a = case a of
  AInt n -> li r n
  AVar v -> load' slots r v
  AGlobal i -> ins ("la " ++ r ++ ", _kc_" ++ show i)
  ANullary t -> modify (\s -> s {gsNullary = S.insert t (gsNullary s)}) >> ins ("la " ++ r ++ ", _kn_" ++ show t)
  AStatic i -> ins ("la " ++ r ++ ", .L_ks_" ++ show i)

-- | Increment a reference count inline (a6, a7). The low 32 bits of the header, as in
-- "Keel.AArch64" (count in bits 10–30): loaded sign-extended, an immortal block is negative.
dup :: Slots -> String -> G ()
dup slots v = do
  lSkip <- newLabel
  load' slots "a6" v
  ins "lw a7, -8(a6)"
  ins ("bltz a7, " ++ lSkip)
  ins "addiw a7, a7, -1024" -- negative: the count was 0, a freed block
  jumpIf "bltz" ["a7"] "_keel_panic_rc"
  ins "addiw a7, a7, 1024"
  ins "addiw a7, a7, 1024"
  ins "sw a7, -8(a6)"
  line (lSkip ++ ":")

expr :: Slots -> Maybe (String, String) -> Expr -> G ()
expr slots join e = case e of
  Ret a -> do
    atom slots "a0" a
    case join of
      Nothing -> leave slots >> ins "ret"
      Just (v, lbl) -> store slots "a0" v >> ins ("j " ++ lbl)
  Bind x rhs (Ret (AVar y)) | x == y, Nothing <- join, Just tc <- tailCall rhs -> tc
  Bind x rhs rest -> do
    rhsCode slots rhs
    store slots "a0" x
    expr slots join rest
  BindIf x c a b rest -> do
    let tailPos = isNothingJ && returns x rest
    lElse <- newLabel
    lJoin <- newLabel
    atom slots "t0" c
    jumpIf "beqz" ["t0"] lElse
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
    atom slots "t0" s
    ins "lw t0, -8(t0)"
    ins "andi t0, t0, 0x3ff" -- the layout, in the header
    forM_ (zip (init bs) labels) $ \((tag, _, _), l) -> do
      li "t1" tag
      jumpIf "beq" ["t0", "t1"] l
    ins ("j " ++ last labels)
    forM_ (zip bs labels) $ \((_, _, body), l) -> do
      line (l ++ ":")
      expr slots (target tailPos x lJoin) body
    unless tailPos $ do
      line (lJoin ++ ":")
      expr slots join rest
  Dup v rest -> dup slots v >> expr slots join rest
  Drop v rest -> do
    load' slots "a0" v
    ins "call _keel_drop"
    expr slots join rest
  DropReuse v mask tok rest -> do
    load' slots "a0" v
    li "a1" mask
    ins "call _keel_drop_reuse"
    store slots "a0" tok
    expr slots join rest
  where
    isNothingJ = case join of
      Nothing -> True
      Just _ -> False
    returns x (Ret (AVar y)) = x == y
    returns _ _ = False
    target tailPos x lJoin = if tailPos then Nothing else Just (x, lJoin)

    tailCall rhs = case rhs of
      RCall f a -> Just $ do
        atom slots "a0" f
        atom slots "a1" a
        ins "ld t6, 0(a0)"
        leave slots
        ins "jr t6"
      RCallKnown i as -> Just $ do
        forM_ (zip [1 :: Int ..] as) $ \(r, a) -> atom slots ("a" ++ show r) a
        if fLoop slots == Just ("_kf_" ++ show i)
          then ins ("j L_kf_" ++ show i ++ "_loop")
          else leave slots >> ins ("tail _kf_" ++ show i)
      RProj a i -> Just $ do
        atom slots "a0" a
        ins "li a1, 0"
        w <- wordSize
        ins ("ld t6, " ++ show (w * i) ++ "(a0)")
        leave slots
        ins "jr t6"
      _ -> Nothing

-- | Allocate a block into a0 (header written). Clobbers a0, a1, t4–t6, a6 only (and a2 on
-- RV32, which passes the header's high half there).
alloc :: Int -> Integer -> G ()
alloc fields lid = do
  t <- gets (\st -> template (gsLayouts st) lid)
  -- A packed layout has fewer words than fields.
  n <- gets (\st -> maybe fields (\(_, w, _) -> w) (keyOf (gsLayouts st) lid))
  li "a0" (toInteger n)
  w <- wordSize
  if w == 8 then li "a1" t else li "a1" (t .&. 0xffffffff) >> li "a2" (t `shiftR` 32)
  ins "call _keel_alloc"

rhsCode :: Slots -> Rhs -> G ()
rhsCode slots rhs = case rhs of
  RAtom a -> atom slots "a0" a
  RPrim op it a b -> do
    atom slots "t0" a
    atom slots "t1" b
    case op of
      Eq -> ins "xor a0, t0, t1" >> ins "seqz a0, a0"
      Lt -> ins ((if signed it then "slt" else "sltu") ++ " a0, t0, t1")
      Arith _ aop | aop `elem` [Div, Rem] -> divide it aop
      Arith ov aop -> arith it ov aop
      Bits bop -> bitwise it bop
  RCall f a -> do
    atom slots "a0" f
    atom slots "a1" a
    ins "ld t6, 0(a0)"
    ins "jalr t6"
  RCallKnown i as -> do
    forM_ (zip [1 :: Int ..] as) $ \(r, a) -> atom slots ("a" ++ show r) a
    ins ("call _kf_" ++ show i)
  RClosure i fvs lid -> do
    alloc (1 + length fvs) lid
    ins ("la t2, _kf_" ++ show i)
    ins "sd t2, 0(a0)"
    storeAll 1 fvs
  RCodata is fvs lid -> do
    alloc (length is + length fvs) lid
    w <- wordSize
    forM_ (zip [0 :: Int ..] is) $ \(j, i) -> do
      ins ("la t2, _kf_" ++ show i)
      ins ("sd t2, " ++ show (w * j) ++ "(a0)")
    storeAll (length is) fvs
  RProj a i -> do
    atom slots "a0" a
    ins "li a1, 0"
    w <- wordSize
    ins ("ld t6, " ++ show (w * i) ++ "(a0)")
    ins "jalr t6"
  RAlloc lid h as -> do
    alloc (length as) lid
    fields lid h as
  RAllocAt tok lid h as -> do
    lFresh <- newLabel
    lDone <- newLabel
    load' slots "a0" tok
    jumpIf "beqz" ["a0"] lFresh
    gets (\st -> header (gsLayouts st) lid) >>= storeHeader "a0"
    ins "la t4, _keel_stats"
    ins "ld t5, 16(t4)"
    ins "addi t5, t5, 1"
    ins "sd t5, 16(t4)"
    ins ("j " ++ lDone)
    line (lFresh ++ ":")
    alloc (length as) lid
    line (lDone ++ ":")
    fields lid h as
  RField a i -> do
    atom slots "t0" a
    w <- wordSize
    ins ("ld a0, " ++ show (w * i) ++ "(t0)")
  RRel a i -> do
    atom slots "t0" a
    ins ("lw t1, " ++ show (4 * i) ++ "(t0)")
    ins "slli t1, t1, 3"
    ins "add a0, t0, t1"
  RHeader a sgn -> atom slots "t0" a >> ins ((if sgn then "lw" else "lwu") ++ " a0, -4(t0)")
  RPushHandler cs lid -> do
    alloc (2 + 2 * length cs) lid
    w <- wordSize
    ins "la t3, _keel_handlers"
    ins "ld t2, 0(t3)"
    ins "sd t2, 0(a0)"
    li "t2" (toInteger (length cs))
    ins ("sd t2, " ++ show w ++ "(a0)")
    forM_ (zip [0 :: Int ..] cs) $ \(i, (n, a)) -> do
      li "t2" (toInteger n)
      ins ("sd t2, " ++ show (w * (2 + 2 * i)) ++ "(a0)")
      atom slots "t2" a
      ins ("sd t2, " ++ show (w * (3 + 2 * i)) ++ "(a0)")
    ins "la t3, _keel_handlers" -- again: loading a variable may have used t3
    ins "sd a0, 0(t3)"
  RPopHandler a -> do
    atom slots "a0" a
    ins "ld t0, 0(a0)"
    ins "la t1, _keel_handlers"
    ins "sd t0, 0(t1)"
    ins "call _keel_drop"
    ins "li a0, 0"
  RPerform n a -> do
    atom slots "a1" a
    li "a0" (toInteger n)
    ins "call _keel_perform"
  RConv to a -> atom slots "a0" a >> canonical to
  -- Arrays: as in "Keel.AArch64".
  RArena True -> ins "call _keel_arena_open"
  RArena False -> ins "call _keel_arena_close"
  RArray ALength _ [a] -> atom slots "t0" a >> ins "ld a0, 0(t0)"
  RArray AGet e [a, i] -> do
    atom slots "t0" a
    atom slots "t1" i
    ins "ld t2, 0(t0)"
    jumpIf "bgeu" ["t1", "t2"] "_keel_panic_bounds" -- unsigned: a negative index is out of bounds too
    element e
  RIndex a i e -> atom slots "t0" a >> atom slots "t1" i >> element e
  RArray op e as -> do
    forM_ (zip [0 :: Int ..] as) $ \(r, a) -> atom slots ("a" ++ show r) a
    case op of
      AEmpty -> li "a0" 0 >> li "a1" (elemKind e) >> ins "call _keel_array_alloc"
      ANew -> li "a2" (elemKind e) >> ins "call _keel_array_new"
      ASet -> ins "call _keel_array_set"
      APush -> ins "call _keel_array_push"
      _ -> ins "call _keel_array_pop"
  where
    storeAll :: Int -> [String] -> G ()
    storeAll from vs = forM_ (zip [from ..] vs) $ \(j, v) -> do
      load' slots "t2" v
      w <- wordSize
      ins ("sd t2, " ++ show (w * j) ++ "(a0)")
    -- A packed layout's pointers go in 4-byte slots after its words, relative to the block.
    fields :: Integer -> Maybe Atom -> [Atom] -> G ()
    fields lid h as = do
      bm <- gets (\st -> maybe 0 (\(_, _, m) -> m) (keyOf (gsLayouts st) lid))
      let nw = fromMaybe (length as) (packedFrom bm (length as))
      w <- wordSize
      forM_ h $ \a -> atom slots "t2" a >> ins "sw t2, -4(a0)"
      forM_ (zip [0 :: Int ..] as) $ \(j, a) -> do
        atom slots "t2" a
        if j < nw
          then ins ("sd t2, " ++ show (w * j) ++ "(a0)")
          else do
            ins "sub t2, t2, a0"
            ins "srai t2, t2, 3"
            ins ("sw t2, " ++ show (4 * (nw + j)) ++ "(a0)")

-- | Load element t1 of array t0 into a0. Elements follow the length and the capacity, and on
-- RV32 every kind is 4 bytes.
element :: Elem -> G ()
element e = do
  w <- wordSize
  ins ("slli t1, t1, " ++ (case e of ENarrow _ -> "2"; _ -> if w == 8 then "3" else "2"))
  ins "add t0, t0, t1"
  ins ((case e of ENarrow True -> "lw"; ENarrow False -> "lwu"; _ -> "ld") ++ " a0, " ++ show (2 * w) ++ "(t0)")

-- | Checked division (t0 / t1 into a0), as in "Keel.AArch64": RISC-V doesn't trap on a zero
-- divisor or on min / -1, so both are checked.
divide :: IntTy -> ArithOp -> G ()
divide it@(IntTy sgn n) aop = do
  xlen <- xlenBits
  jumpIf "beqz" ["t1"] "_keel_panic_div"
  when (sgn && n == xlen && aop == Div) $ do
    lOk <- newLabel
    ins "li t2, -1"
    ins ("bne t1, t2, " ++ lOk)
    li "t2" (fst (intRange it))
    jumpIf "beq" ["t0", "t2"] "_keel_panic_overflow"
    line (lOk ++ ":")
  ins ((case aop of Div -> "div"; _ -> "rem") ++ (if sgn then "" else "u") ++ " a0, t0, t1")
  when (sgn && n < xlen && aop == Div) $ do
    li "t2" (snd (intRange it))
    jumpIf "bgt" ["a0", "t2"] "_keel_panic_overflow"

-- | Re-extend a0 to the canonical form of an integer type.
canonical :: IntTy -> G ()
canonical (IntTy sgn n) = xlenBits >>= extend
  where
    extend xlen
      | n >= xlen = pure ()
      | sgn = ins ("slli a0, a0, " ++ sh) >> ins ("srai a0, a0, " ++ sh)
      | n == 8 = ins "andi a0, a0, 255"
      | otherwise = ins ("slli a0, a0, " ++ sh) >> ins ("srli a0, a0, " ++ sh)
      where
        sh = show (xlen - n)

-- | Arithmetic with t0, t1 as operands and the result in a0 (spec §2.5). RISC-V has no flags,
-- so overflow is computed from the operands and the result.
arith :: IntTy -> Overflow -> ArithOp -> G ()
arith it ov aop = xlenBits >>= \xlen -> arithAt xlen it ov aop

arithAt :: Int -> IntTy -> Overflow -> ArithOp -> G ()
arithAt xlen it@(IntTy sgn n) ov aop
  | ov == Wrap = plain >> when narrow (canonical it)
  | otherwise = do
      lOvf <- if ov == Checked then pure "_keel_panic_overflow" else newLabel
      detect lOvf
      case ov of
        Saturate -> do
          lDone <- newLabel
          ins ("j " ++ lDone)
          line (lOvf ++ ":")
          saturate
          line (lDone ++ ":")
        Optional -> do
          lDone <- newLabel
          (none, some) <- gets (\st -> optionLayouts (gsLayouts st) it)
          ins "mv t3, a0"
          if n <= 32
            then alloc 0 some >> ins "sw t3, -4(a0)"
            else alloc 1 some >> ins "sd t3, 0(a0)"
          ins ("j " ++ lDone)
          line (lOvf ++ ":")
          atom (Slots M.empty [] Nothing) "a0" (ANullary none)
          line (lDone ++ ":")
        _ -> pure ()
  where
    narrow = n < xlen
    (lo, hi) = intRange it
    opName = case aop of
      Add -> "add"
      Sub -> "sub"
      _ -> "mul"
    plain = ins (opName ++ " a0, t0, t1")
    detect lOvf
      | narrow && sgn = do
          plain
          li "t2" lo
          jumpIf "blt" ["a0", "t2"] lOvf
          li "t2" hi
          jumpIf "bgt" ["a0", "t2"] lOvf
      | narrow = do
          plain
          li "t2" hi
          jumpIf "bgtu" ["a0", "t2"] lOvf
      | otherwise = case (aop, sgn) of
          -- signed: the result's sign is wrong exactly when an overflow happened
          (Add, True) -> do
            ins "add a0, t0, t1"
            ins "xor t2, t0, a0"
            ins "xor t3, t1, a0"
            ins "and t2, t2, t3"
            jumpIf "bltz" ["t2"] lOvf
          (Sub, True) -> do
            ins "sub a0, t0, t1"
            ins "xor t2, t0, t1"
            ins "xor t3, t0, a0"
            ins "and t2, t2, t3"
            jumpIf "bltz" ["t2"] lOvf
          (_, True) -> do -- Mul (division never reaches here: see divide)
            ins "mul a0, t0, t1"
            ins "mulh t2, t0, t1"
            ins ("srai t3, a0, " ++ show (xlen - 1))
            jumpIf "bne" ["t2", "t3"] lOvf
          (Add, False) -> ins "add a0, t0, t1" >> jumpIf "bltu" ["a0", "t0"] lOvf
          (Sub, False) -> ins "sub a0, t0, t1" >> jumpIf "bltu" ["t0", "t1"] lOvf
          (_, False) -> do -- Mul
            ins "mul a0, t0, t1"
            ins "mulhu t2, t0, t1"
            jumpIf "bnez" ["t2"] lOvf
    saturate
      | narrow && sgn = do
          lLow <- newLabel
          lEnd <- newLabel
          li "t2" lo
          ins ("blt a0, t2, " ++ lLow)
          li "a0" hi
          ins ("j " ++ lEnd)
          line (lLow ++ ":")
          ins "mv a0, t2"
          line (lEnd ++ ":")
      | not sgn = if aop == Sub then ins "li a0, 0" else li "a0" hi
      | otherwise = do
          lEnd <- newLabel
          if aop == Mul then ins "xor t4, t0, t1" else ins "mv t4, t0"
          li "a0" hi
          ins ("bgez t4, " ++ lEnd)
          li "a0" lo
          line (lEnd ++ ":")

bitwise :: IntTy -> BitOp -> G ()
bitwise it@(IntTy sgn _) bop = case bop of
  And -> ins "and a0, t0, t1"
  Or -> ins "or a0, t0, t1"
  Xor -> ins "xor a0, t0, t1"
  Shl -> shift "sll" >> canonical it
  Shr -> shift (if sgn then "sra" else "srl")
  where
    shift instr = do
      lPos <- newLabel
      lBig <- newLabel
      lDone <- newLabel
      when sgn $ do
        ins ("bgez t1, " ++ lPos)
        ins "li t1, 0"
      line (lPos ++ ":")
      xlen <- xlenBits
      li "t2" (toInteger xlen - 1)
      ins ("bgtu t1, t2, " ++ lBig)
      ins (instr ++ " a0, t0, t1")
      ins ("j " ++ lDone)
      line (lBig ++ ":")
      if instr == "sra" then ins ("srai a0, t0, " ++ show (xlen - 1)) else ins "li a0, 0"
      line (lDone ++ ":")

-- Results ---------------------------------------------------------------------------------

emitPrinter :: [Decl] -> M.Map String (Ty, String) -> String -> Ty -> G ()
emitPrinter decls printers lbl t = do
  line "\t.p2align 2"
  line (lbl ++ ":\t\t\t# print " ++ prettyTy t)
  ins "addi sp, sp, -16"
  ins "sd ra, 8(sp)"
  ins "sd s0, 0(sp)"
  ins "mv s0, sp"
  ins "addi sp, sp, -16"
  ins "sd a0, 0(sp)" -- the value
  case t of
    TInt (IntTy sgn _) -> ins (if sgn then "call _keel_print_i64" else "call _keel_print_u64")
    TBool -> do
      lFalse <- newLabel
      lDone <- newLabel
      ins ("beqz a0, " ++ lFalse)
      printStr "true"
      ins ("j " ++ lDone)
      line (lFalse ++ ":")
      printStr "false"
      line (lDone ++ ":")
    TUnit -> printStr "()"
    TBox a -> printStr "box " >> field (Right (-1, False)) a
    TPair a b -> do
      printStr "("
      field (Right (0, False)) a
      printStr ", "
      field (Right (1, False)) b
      printStr ")"
    TData d tys | Just (ps, cs) <- dataOf decls d -> do
      let inst = substTy (M.fromList (zip ps tys)) M.empty
      layouts <- gets gsLayouts
      w <- wordSize
      -- As in "Keel.AArch64": constructors never built at this type have no block to print.
      let built = [(c, fts, lid, h, ws) | (c, fs) <- cs, let fts = map inst fs, let (key, h, ws) = dataLayoutKey (8 * w) (conNumbers decls M.! c) fts, Just lid <- [M.lookup key layouts]]
      lDone <- newLabel
      labels <- mapM (const newLabel) built
      ins "ld t0, 0(sp)"
      ins "lw t0, -8(t0)"
      ins "andi t0, t0, 0x3ff"
      forM_ (zip built labels) $ \((_, _, lid, _, _), l) -> do
        li "t1" lid
        jumpIf "beq" ["t0", "t1"] l
      ins ("j " ++ lDone)
      forM_ (zip built labels) $ \((c, fts, lid, h, ws), l) -> do
        line (l ++ ":")
        printStr c
        unless (null fts) $ do
          printStr "("
          forM_ (zip [0 :: Int ..] fts) $ \(i, ft) -> do
            when (i > 0) $ printStr ", "
            let w = fromMaybe i (elemIndex i ws)
                rel = case keyOf layouts lid of
                  Just (_, _, bm) | Just nw <- packedFrom bm (length ws), w >= nw -> Just (nw + w)
                  _ -> Nothing
            field (if h == Just i then Left (case ft of TInt it -> signed it; _ -> False) else Right (maybe (w, False) (,True) rel)) ft
          printStr ")"
        ins ("j " ++ lDone)
      line (lDone ++ ":")
    TData "Array" [a] -> do
      lLoop <- newLabel
      lFirst <- newLabel
      lDone <- newLabel
      printStr "["
      ins "sd zero, 8(sp)" -- the index
      line (lLoop ++ ":")
      ins "ld t0, 0(sp)"
      ins "ld t1, 8(sp)"
      ins "ld t2, 0(t0)"
      jumpIf "bgeu" ["t1", "t2"] lDone
      jumpIf "beqz" ["t1"] lFirst
      printStr ", "
      line (lFirst ++ ":")
      ins "ld t0, 0(sp)"
      ins "ld t1, 8(sp)"
      element (elemOf a)
      maybe (printStr "...") (\(_, l) -> ins ("call " ++ l)) (M.lookup (prettyTy a) printers)
      ins "ld t1, 8(sp)"
      ins "addi t1, t1, 1"
      ins "sd t1, 8(sp)"
      ins ("j " ++ lLoop)
      line (lDone ++ ":")
      printStr "]"
    TData _ _ -> printStr "<codata>"
    _ -> printStr "<closure>"
  epilogue
  ins "ret"
  where
    -- Word i of the block (-1: the value itself; with True, packed pointer slot i), or its
    -- header field (Left: whether signed).
    field :: Either Bool (Int, Bool) -> Ty -> G ()
    field place ft = do
      ins "ld a0, 0(sp)"
      case place of
        Left sgn -> ins ((if sgn then "lw" else "lwu") ++ " a0, -4(a0)")
        Right (i, True) -> ins ("lw t0, " ++ show (4 * i) ++ "(a0)") >> ins "slli t0, t0, 3" >> ins "add a0, a0, t0"
        Right (i, _) -> when (i >= 0) $ wordSize >>= \w -> ins ("ld a0, " ++ show (w * i) ++ "(a0)")
      case M.lookup (prettyTy ft) printers of
        Just (_, l) -> ins ("call " ++ l)
        Nothing -> printStr "..."

-- | The Pico 2's entry point, at the image's first byte: past the IMAGE_DEF block that marks
-- the image as an RP2350 RISC-V executable (picobin, datasheet §5.9; within the first 4 KB),
-- set up the stack, copy the variables from flash to SRAM, and run main. Nothing reads its
-- value: when it returns, the core sleeps.
emitBoot :: G ()
emitBoot = do
  line "\t.globl _start"
  line "\t.p2align 2"
  line "_start:"
  ins "j .L_boot"
  line "\t.p2align 2"
  ins ".word 0xffffded3\t\t# block start"
  ins ".byte 0x42, 0x01\t\t# item: image type, 1 word"
  ins ".hword 0x1121\t\t# executable, secure, RISC-V, RP2350"
  ins ".byte 0xff\t\t# the last item"
  ins ".hword 0x0001\t\t# the items before it, in words"
  ins ".byte 0x00"
  ins ".word 0x00000000\t\t# the next block: none (a loop of one)"
  ins ".word 0xab123579\t\t# block end"
  line ".L_boot:"
  ins "la sp, _keel_stack_top"
  ins "la t0, _keel_data_load"
  ins "la t1, _keel_data"
  ins "la t2, _keel_data_end"
  line ".L_boot_copy:"
  ins "bgeu t1, t2, .L_boot_run"
  ins "lw t3, 0(t0)"
  ins "sw t3, 0(t1)"
  ins "addi t0, t0, 4"
  ins "addi t1, t1, 4"
  ins "j .L_boot_copy"
  line ".L_boot_run:"
  ins "li a0, 0"
  ins "call _kf_main"
  ins "li a0, 0"
  ins "tail _keel_exit"

-- | Entry point: set up the stack, run main, print the result and the allocator counters
-- (always: there is no environment to ask), then exit through the test device.
emitStart :: M.Map String (Ty, String) -> Ty -> G ()
emitStart printers t = do
  line "\t.globl _start"
  line "\t.p2align 2"
  line "_start:"
  ins "la sp, _keel_stack_top"
  ins "li a0, 0"
  ins "call _kf_main"
  ins "addi sp, sp, -16"
  ins "sd a0, 0(sp)"
  printStr "result: "
  ins "ld a0, 0(sp)"
  forM_ (M.lookup (prettyTy t) printers) $ \(_, l) -> ins ("call " ++ l)
  printStr "\n"
  when (isPtr t) $ ins "ld a0, 0(sp)" >> ins "call _keel_drop"
  printStr "keel-stats:"
  forM_ (zip ["allocs", "recycled", "inplace", "freed"] [0 :: Int, 8, 16, 24]) $ \(name, off) -> do
    printStr (" " ++ name ++ "=")
    ins "la t0, _keel_stats"
    ins ("ld a0, " ++ show off ++ "(t0)")
    ins "call _keel_print_u64"
  printStr " live="
  ins "la t0, _keel_stats"
  ins "ld t1, 0(t0)"
  ins "ld t2, 8(t0)"
  ins "add t1, t1, t2"
  ins "ld t2, 16(t0)"
  ins "add t1, t1, t2"
  ins "ld t2, 24(t0)"
  ins "sub a0, t1, t2"
  ins "call _keel_print_i64"
  printStr "\n"
  ins "li a0, 0"
  ins "tail _keel_exit"

-- Runtime ---------------------------------------------------------------------------------

emitRuntime :: G ()
emitRuntime = do
  w <- wordSize
  sh <- wordShift
  console <- gets ((/= Pico2) . gsBoard)
  let wd k = show (k * w) -- the byte offset of word k
      rv32 = w == 4
  -- _keel_alloc: a0 = payload words, a1 = header without its count (on RV32 its low half, and
  -- a2 the high one) → a0 = payload. Clobbers t4–t6, a6.
  fn "_keel_alloc"
  li "t4" (toInteger maxSmall)
  ins "bgtu a0, t4, .L_alloc_bump"
  ins "la t4, _keel_fl" -- the free lists, or an empty table while an arena is open
  ins "ld t4, 0(t4)"
  ins "slli t5, a0, 3"
  ins "add t4, t4, t5"
  ins "ld t5, 0(t4)"
  ins "beqz t5, .L_alloc_bump"
  ins "beqz a0, .L_alloc_link0"
  ins "ld t6, 0(t5)" -- the next free block
  line ".L_alloc_pop:"
  ins "sd t6, 0(t4)"
  stat 8
  ins "j .L_alloc_header"
  line ".L_alloc_bump:"
  ins "la t4, _keel_heap_ptr"
  ins "ld t5, 0(t4)"
  ins ("slli t6, a0, " ++ show sh)
  ins "add t6, t6, t5"
  ins "addi t6, t6, 8"
  ins "ld a6, 8(t4)"
  jumpIf "bgtu" ["t6", "a6"] "_keel_panic_oom"
  ins "sd t6, 0(t4)"
  ins "addi t5, t5, 8"
  stat 0
  line ".L_alloc_header:"
  ins "ori t6, a1, 1024" -- count 1
  ins "sd t6, -8(t5)"
  when rv32 $ ins "sw a2, -4(t5)"
  ins "mv a0, t5"
  ins "ret"
  -- A block of no words links to the next in its header's high half, in words from it.
  line ".L_alloc_link0:"
  ins "lw t6, -4(t5)"
  ins "beqz t6, .L_alloc_pop"
  ins ("slli t6, t6, " ++ show sh)
  ins "add t6, t6, t5"
  ins "j .L_alloc_pop"

  -- Arenas: as in "Keel.AArch64".
  fn "_keel_arena_open"
  ins "la t4, _keel_heap_ptr"
  ins "ld t5, 0(t4)"
  ins "addi t6, t5, 24"
  ins "ld a6, 8(t4)"
  jumpIf "bgtu" ["t6", "a6"] "_keel_panic_oom"
  ins "sd t6, 0(t4)"
  ins "la t4, _keel_arena_base"
  ins "ld t6, 0(t4)"
  ins "sd t6, 0(t5)"
  ins "la a6, _keel_arena_top"
  ins "ld a1, 0(a6)"
  ins "sd a1, 8(t5)"
  ins "sd t5, 0(a6)"
  ins "la a1, _keel_stats"
  ins "ld a1, 0(a1)"
  ins "sd a1, 16(t5)"
  jumpIf "bltu" ["t6", "t5"] ".L_arena_keep"
  ins "sd t5, 0(t4)"
  line ".L_arena_keep:"
  ins "la t4, _keel_nofree"
  ins "la t5, _keel_fl"
  ins "sd t4, 0(t5)"
  ins "li a0, 0"
  ins "ret"

  fn "_keel_arena_close"
  ins "la a6, _keel_arena_top"
  ins "ld t5, 0(a6)"
  ins "ld t6, 8(t5)"
  ins "sd t6, 0(a6)"
  ins "ld t6, 0(t5)"
  ins "la t4, _keel_arena_base"
  ins "sd t6, 0(t4)"
  ins "addi t6, t6, 1" -- the outermost arena closed: the free lists are back
  jumpIf "bnez" ["t6"] ".L_close_inner"
  ins "la t4, _keel_freelists"
  ins "la t6, _keel_fl"
  ins "sd t4, 0(t6)"
  line ".L_close_inner:"
  ins "la t4, _keel_stats"
  ins "ld t6, 0(t4)"
  ins "ld a1, 16(t5)"
  ins "sub t6, t6, a1"
  ins "ld a1, 24(t4)"
  ins "add a1, a1, t6"
  ins "sd a1, 24(t4)"
  ins "ld a1, 8(t5)" -- … and not again when the enclosing arena closes
  jumpIf "beqz" ["a1"] ".L_close_outermost"
  ins "ld a6, 16(a1)"
  ins "add a6, a6, t6"
  ins "sd a6, 16(a1)"
  line ".L_close_outermost:"
  ins "la t4, _keel_heap_ptr"
  ins "sd t5, 0(t4)"
  ins "li a0, 0"
  ins "ret"

  -- _keel_drop: a0 = block; the last pointer child is handled by looping.
  fn "_keel_drop"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  line ".L_drop_top:"
  ins "lw t0, -8(a0)"
  ins "bltz t0, .L_drop_ret"
  ins "addiw t0, t0, -1024"
  jumpIf "bltz" ["t0"] "_keel_panic_rc" -- the count was 0: a freed block
  ins "sw t0, -8(a0)"
  ins "srliw t1, t0, 10"
  ins "bnez t1, .L_drop_ret"
  ins "la t3, _keel_arena_base"
  ins "ld t3, 0(t3)"
  jumpIf "bgeu" ["a0", "t3"] ".L_drop_ret" -- in an open arena: freed when it closes
  stat 24
  ins "sd a0, 0(sp)"
  ins "andi t3, t0, 0x3ff"
  li "t1" arrayLayout
  ins "bgeu t3, t1, .L_drop_special"
  headerMap "t2" "a0"
  splitPacked
  line ".L_drop_loop:"
  ins "beqz t2, .L_drop_free"
  ins "addi t3, t2, -1"
  ins "and t3, t2, t3"
  ins "beqz t3, .L_drop_last" -- one pointer child left
  ins "neg t3, t2"
  ins "and t3, t2, t3" -- lowest set bit
  ins "xor t2, t2, t3"
  ins "sd t2, 8(sp)"
  lowIndex
  ins "ld t0, 0(sp)"
  child "a0" "t0"
  ins "call _keel_drop"
  ins "ld t2, 8(sp)"
  ins "j .L_drop_loop"
  line ".L_drop_last:"
  ins "mv t3, t2"
  lowIndex
  ins "ld a0, 0(sp)"
  child "t0" "a0"
  ins "sd t0, 8(sp)"
  ins "call _keel_free_block"
  ins "ld a0, 8(sp)"
  ins "j .L_drop_top"
  line ".L_drop_free:"
  ins "ld a0, 0(sp)"
  ins "call _keel_free_block"
  line ".L_drop_ret:"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"
  -- A block with a field in its header: its pointer map is in the table.
  line ".L_drop_special:"
  li "t4" fieldLayouts
  ins "bltu t3, t4, .L_drop_array"
  pointerMap
  splitPacked
  ins "j .L_drop_loop"
  -- An array: drop its elements if they are pointers, last first, then free it.
  line ".L_drop_array:"
  li "t1" (arrayLayout + 2)
  ins "beq t3, t1, .L_drop_elems_ptr"
  ins "j .L_drop_free"
  line ".L_drop_elems_ptr:"
  ins "ld t2, 0(a0)"
  line ".L_drop_elems:"
  ins "beqz t2, .L_drop_free"
  ins "addi t2, t2, -1"
  ins "sd t2, 8(sp)"
  ins "ld t0, 0(sp)"
  ins ("slli t3, t2, " ++ show sh)
  ins "add t0, t0, t3"
  ins ("ld a0, " ++ wd 2 ++ "(t0)")
  ins "call _keel_drop"
  ins "ld t2, 8(sp)"
  ins "j .L_drop_elems"

  -- _keel_free_block: a0 = block with count 0 → its size's free list.
  fn "_keel_free_block"
  ins "lbu t0, -4(a0)" -- its words (an array's: capped at 255)
  ins "lw t1, -8(a0)"
  ins "andi t1, t1, 0x200" -- fieldLayouts = 512: the header holds a field
  ins "beqz t1, .L_free_size"
  ins "lw t0, -8(a0)"
  ins "andi t0, t0, 0x1ff"
  ins "la t1, _keel_layouts"
  ins "slli t0, t0, 2"
  ins "add t1, t1, t0"
  ins "lbu t0, 0(t1)"
  line ".L_free_size:"
  li "t1" (toInteger maxSmall)
  ins "bgtu t0, t1, .L_free_ret"
  ins "la t1, _keel_freelists"
  ins "slli t0, t0, 3"
  ins "add t1, t1, t0"
  ins "ld t2, 0(t1)"
  ins "beqz t0, .L_free_link0"
  ins "sd t2, 0(a0)" -- the link, in the first word
  ins "sd a0, 0(t1)"
  ins "ret"
  -- A block of no words: the link in its header's high half, in words from it (0: none).
  line ".L_free_link0:"
  ins "beqz t2, .L_free_link"
  ins "sub t2, t2, a0"
  ins ("srai t2, t2, " ++ show sh)
  line ".L_free_link:"
  ins "sw t2, -4(a0)"
  ins "sd a0, 0(t1)"
  line ".L_free_ret:"
  ins "ret"

  -- Arrays: as in "Keel.AArch64" (payload [length, capacity, elements…]; the layout is
  -- arrayLayout plus the kind: 0 for 4-byte elements, 1 words, 2 pointers).

  -- _keel_array_alloc: a0 = capacity, a1 = kind → a0 = an empty array.
  fn "_keel_array_alloc"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  ins "sd a0, 0(sp)"
  ins "sd a1, 8(sp)"
  elemWords "a0" "a0" "a1" "t0"
  ins "sd a0, 16(sp)"
  ins "li a1, 0"
  ins "call _keel_alloc"
  ins "ld t0, 0(sp)"
  ins "ld t1, 8(sp)"
  li "t2" (1024 + arrayLayout) -- count 1, the kind's layout
  ins "add t2, t2, t1"
  ins "ld t3, 16(sp)" -- its words, capped at 255
  ins "li t4, 0xFF"
  ins "bltu t3, t4, .L_aalloc_size"
  ins "mv t3, t4"
  line ".L_aalloc_size:"
  if rv32
    then ins "sw t2, -8(a0)" >> ins "sw t3, -4(a0)"
    else ins "slli t3, t3, 32" >> ins "or t2, t2, t3" >> ins "sd t2, -8(a0)"
  ins "sd zero, 0(a0)"
  ins ("sd t0, " ++ wd 1 ++ "(a0)")
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"

  -- _keel_array_new: a0 = length, a1 = the element (owned), a2 = kind → a0.
  fn "_keel_array_new"
  ins "addi sp, sp, -48"
  ins "sd ra, 40(sp)"
  jumpIf "bltz" ["a0"] "_keel_panic_bounds"
  ins "sd a1, 0(sp)"
  ins "sd a2, 8(sp)"
  ins "sd a0, 16(sp)"
  ins "mv a1, a2"
  ins "call _keel_array_alloc"
  ins "ld t0, 16(sp)"
  ins "ld t1, 0(sp)"
  ins "ld t2, 8(sp)"
  ins "sd t0, 0(a0)"
  ins "li t3, 0"
  ins "beqz t2, .L_anew_fill4"
  line ".L_anew_fill:"
  ins "bgeu t3, t0, .L_anew_filled"
  ins ("slli t4, t3, " ++ show sh)
  ins "add t4, t4, a0"
  ins ("sd t1, " ++ wd 2 ++ "(t4)")
  ins "addi t3, t3, 1"
  ins "j .L_anew_fill"
  line ".L_anew_fill4:"
  ins "bgeu t3, t0, .L_anew_filled"
  ins "slli t4, t3, 2"
  ins "add t4, t4, a0"
  ins ("sw t1, " ++ wd 2 ++ "(t4)")
  ins "addi t3, t3, 1"
  ins "j .L_anew_fill4"
  line ".L_anew_filled:"
  ins "li t3, 2"
  ins "bne t2, t3, .L_anew_ret"
  -- The element now has n references in the array; the caller gave one.
  ins "beqz t0, .L_anew_drop"
  ins "lw t4, -8(t1)"
  ins "bltz t4, .L_anew_ret"
  ins "srliw t5, t4, 10" -- the count
  ins "add t5, t5, t0"
  ins "addi t5, t5, -1"
  ins "andi t4, t4, 0x3ff"
  ins "srli t6, t5, 21"
  ins "beqz t6, .L_anew_count"
  ins "li t5, 0x200000" -- overflowed: immortal (bit 31 after the shift)
  line ".L_anew_count:"
  ins "slli t5, t5, 10"
  ins "or t4, t4, t5"
  ins "sw t4, -8(t1)"
  ins "j .L_anew_ret"
  line ".L_anew_drop:"
  ins "sd a0, 16(sp)"
  ins "mv a0, t1"
  ins "call _keel_drop"
  ins "ld a0, 16(sp)"
  line ".L_anew_ret:"
  ins "ld ra, 40(sp)"
  ins "addi sp, sp, 48"
  ins "ret"

  -- _keel_array_clone: a0 = array (owned), a1 = capacity ≥ its length → a0 = a fresh copy;
  -- a unique array's elements move and its block is freed, a shared one's are duplicated.
  fn "_keel_array_clone"
  ins "addi sp, sp, -48"
  ins "sd ra, 40(sp)"
  ins "sd a0, 0(sp)"
  ins "lw t0, -8(a0)"
  ins "andi t0, t0, 0x3ff"
  ins ("addi t0, t0, -" ++ show arrayLayout) -- the kind
  ins "sd t0, 16(sp)"
  ins "mv a0, a1"
  ins "mv a1, t0"
  ins "call _keel_array_alloc"
  ins "ld t0, 0(sp)"
  ins "ld t1, 0(t0)"
  ins "sd t1, 0(a0)"
  -- Copy the elements' words.
  ins "ld t2, 16(sp)"
  elemWords "t6" "t1" "t2" "t3"
  ins "addi t6, t6, -2"
  ins "li t2, 0"
  line ".L_aclone_copy:"
  ins "bgeu t2, t6, .L_aclone_copied"
  ins ("slli t3, t2, " ++ show sh)
  ins "add t4, t0, t3"
  ins ("ld t5, " ++ wd 2 ++ "(t4)")
  ins "add t4, a0, t3"
  ins ("sd t5, " ++ wd 2 ++ "(t4)")
  ins "addi t2, t2, 1"
  ins "j .L_aclone_copy"
  line ".L_aclone_copied:"
  ins "lw t2, -8(t0)"
  ins "srliw t3, t2, 10"
  ins "li t4, 1"
  ins "bne t3, t4, .L_aclone_shared"
  ins "andi t3, t2, 0x3ff" -- count 0
  ins "sw t3, -8(t0)"
  ins "la t1, _keel_arena_base"
  ins "ld t1, 0(t1)"
  jumpIf "bgeu" ["t0", "t1"] ".L_aclone_ret" -- in an open arena: freed when it closes
  stat 24
  ins "sd a0, 8(sp)"
  ins "mv a0, t0"
  ins "call _keel_free_block"
  ins "ld a0, 8(sp)"
  ins "j .L_aclone_ret"
  line ".L_aclone_shared:"
  ins "andi t3, t2, 0x3ff"
  ins ("addi t3, t3, -" ++ show (arrayLayout + 2))
  ins "bnez t3, .L_aclone_dec"
  ins "li t3, 0"
  line ".L_aclone_dup:"
  ins "bgeu t3, t1, .L_aclone_dec"
  ins ("slli t4, t3, " ++ show sh)
  ins "add t4, t4, t0"
  ins ("ld t4, " ++ wd 2 ++ "(t4)")
  ins "lw t5, -8(t4)"
  ins "bltz t5, .L_aclone_next"
  ins "addiw t5, t5, 1024"
  ins "sw t5, -8(t4)"
  line ".L_aclone_next:"
  ins "addi t3, t3, 1"
  ins "j .L_aclone_dup"
  line ".L_aclone_dec:"
  ins "addiw t2, t2, -1024"
  ins "sw t2, -8(t0)"
  line ".L_aclone_ret:"
  ins "ld ra, 40(sp)"
  ins "addi sp, sp, 48"
  ins "ret"

  -- _keel_array_set: a0 = array (owned), a1 = index, a2 = element (owned) → a0.
  fn "_keel_array_set"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  ins "ld t0, 0(a0)"
  jumpIf "bgeu" ["a1", "t0"] "_keel_panic_bounds"
  ins "lw t1, -8(a0)"
  ins "srliw t1, t1, 10"
  ins "li t2, 1"
  ins "beq t1, t2, .L_aset_store"
  ins "sd a1, 0(sp)"
  ins "sd a2, 8(sp)"
  ins ("ld a1, " ++ wd 1 ++ "(a0)")
  ins "call _keel_array_clone"
  ins "ld a1, 0(sp)"
  ins "ld a2, 8(sp)"
  line ".L_aset_store:"
  ins "lw t2, -8(a0)"
  ins "andi t2, t2, 0x3ff"
  ins ("addi t2, t2, -" ++ show arrayLayout)
  ins "bnez t2, .L_aset_word"
  ins "slli t0, a1, 2"
  ins "add t0, t0, a0"
  ins ("sw a2, " ++ wd 2 ++ "(t0)")
  ins "j .L_aset_ret"
  line ".L_aset_word:"
  ins ("slli t0, a1, " ++ show sh)
  ins "add t0, t0, a0"
  ins ("ld t1, " ++ wd 2 ++ "(t0)")
  ins ("sd a2, " ++ wd 2 ++ "(t0)")
  ins "addi t2, t2, -2"
  ins "bnez t2, .L_aset_ret"
  ins "sd a0, 0(sp)"
  ins "mv a0, t1"
  ins "call _keel_drop" -- the element it replaced
  ins "ld a0, 0(sp)"
  line ".L_aset_ret:"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"

  -- _keel_array_push: a0 = array (owned), a1 = element (owned) → a0. A full array doubles.
  fn "_keel_array_push"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  ins "sd a1, 0(sp)"
  ins "ld t0, 0(a0)"
  ins ("ld t1, " ++ wd 1 ++ "(a0)")
  ins "bgeu t0, t1, .L_apush_grow"
  ins "lw t2, -8(a0)"
  ins "srliw t2, t2, 10"
  ins "li t3, 1"
  ins "beq t2, t3, .L_apush_store"
  ins "mv a1, t1"
  ins "call _keel_array_clone"
  ins "j .L_apush_store"
  line ".L_apush_grow:"
  ins "slli a1, t1, 1"
  ins "li t3, 4"
  ins "bgeu a1, t3, .L_apush_cap"
  ins "mv a1, t3"
  line ".L_apush_cap:"
  ins "call _keel_array_clone"
  line ".L_apush_store:"
  ins "ld t0, 0(a0)"
  ins "ld a1, 0(sp)"
  ins "lw t2, -8(a0)"
  ins "andi t2, t2, 0x3ff"
  ins ("addi t2, t2, -" ++ show arrayLayout)
  ins "bnez t2, .L_apush_word"
  ins "slli t1, t0, 2"
  ins "add t1, t1, a0"
  ins ("sw a1, " ++ wd 2 ++ "(t1)")
  ins "j .L_apush_count"
  line ".L_apush_word:"
  ins ("slli t1, t0, " ++ show sh)
  ins "add t1, t1, a0"
  ins ("sd a1, " ++ wd 2 ++ "(t1)")
  line ".L_apush_count:"
  ins "addi t0, t0, 1"
  ins "sd t0, 0(a0)"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"

  -- _keel_array_pop: a0 = array (owned) → a0 without its last element.
  fn "_keel_array_pop"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  ins "ld t0, 0(a0)"
  jumpIf "beqz" ["t0"] "_keel_panic_bounds"
  ins "lw t1, -8(a0)"
  ins "srliw t1, t1, 10"
  ins "li t2, 1"
  ins "beq t1, t2, .L_apop_take"
  ins ("ld a1, " ++ wd 1 ++ "(a0)")
  ins "call _keel_array_clone"
  line ".L_apop_take:"
  ins "ld t0, 0(a0)"
  ins "addi t0, t0, -1"
  ins "sd t0, 0(a0)"
  ins "lw t2, -8(a0)"
  ins "andi t2, t2, 0x3ff"
  ins ("addi t2, t2, -" ++ show (arrayLayout + 2))
  ins "bnez t2, .L_apop_ret"
  ins ("slli t1, t0, " ++ show sh)
  ins "add t1, t1, a0"
  ins "sd a0, 0(sp)"
  ins ("ld a0, " ++ wd 2 ++ "(t1)")
  ins "call _keel_drop"
  ins "ld a0, 0(sp)"
  line ".L_apop_ret:"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"

  -- _keel_drop_reuse: a0 = block, a1 = the fields taken over (a mask of words) → the block if
  -- it was unique (its other children dropped), else 0 (the fields taken over duplicated).
  fn "_keel_drop_reuse"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  ins "lw t0, -8(a0)"
  ins "bltz t0, .L_reuse_none"
  ins "srliw t1, t0, 10"
  jumpIf "beqz" ["t1"] "_keel_panic_rc"
  ins "li t2, 1"
  ins "bne t1, t2, .L_reuse_shared"
  stat 24
  ins "sd a0, 0(sp)"
  reuseMap
  ins "not t4, a1" -- the fields taken over stay alive: they are the caller's now
  ins "and t2, t2, t4"
  line ".L_reuse_loop:"
  ins "beqz t2, .L_reuse_done"
  ins "neg t3, t2"
  ins "and t3, t2, t3"
  ins "xor t2, t2, t3"
  ins "sd t2, 8(sp)"
  lowIndex
  ins "ld t0, 0(sp)"
  child "a0" "t0"
  ins "call _keel_drop"
  ins "ld t2, 8(sp)"
  ins "j .L_reuse_loop"
  line ".L_reuse_done:"
  ins "ld a0, 0(sp)"
  ins "lw t0, -8(a0)"
  ins "andi t0, t0, 0x3ff" -- count 0 until reused
  ins "sw t0, -8(a0)"
  ins "j .L_reuse_ret"
  line ".L_reuse_shared:"
  ins "addiw t0, t0, -1024"
  ins "sw t0, -8(a0)"
  -- The block keeps its references: duplicate the fields taken over.
  line ".L_reuse_none:"
  ins "beqz a1, .L_reuse_zero"
  reuseMap -- only for its packed bit
  line ".L_reuse_dup:"
  ins "neg t3, a1"
  ins "and t3, a1, t3" -- lowest set bit
  ins "xor a1, a1, t3"
  lowIndex
  child "t4" "a0"
  ins "lw t5, -8(t4)"
  ins "bltz t5, .L_reuse_next"
  ins "addiw t5, t5, 1024"
  ins "sw t5, -8(t4)"
  line ".L_reuse_next:"
  ins "bnez a1, .L_reuse_dup"
  line ".L_reuse_zero:"
  ins "li a0, 0"
  line ".L_reuse_ret:"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"

  -- _keel_perform: a0 = operation number, a1 = argument → a0 = result.
  fn "_keel_perform"
  ins "addi sp, sp, -32"
  ins "sd ra, 24(sp)"
  ins "la t0, _keel_handlers"
  ins "ld t1, 0(t0)"
  ins "sd t1, 0(sp)" -- restored afterwards
  line ".L_perform_frame:"
  ins "beqz t1, .L_perform_machine"
  ins ("ld t2, " ++ wd 1 ++ "(t1)")
  ins ("addi t3, t1, " ++ wd 2)
  line ".L_perform_scan:"
  ins "beqz t2, .L_perform_next"
  ins "ld t4, 0(t3)"
  ins "beq t4, a0, .L_perform_found"
  ins ("addi t3, t3, " ++ wd 2)
  ins "addi t2, t2, -1"
  ins "j .L_perform_scan"
  line ".L_perform_next:"
  ins "ld t1, 0(t1)"
  ins "j .L_perform_frame"
  line ".L_perform_found:"
  ins "ld t4, 0(t1)"
  ins "sd t4, 0(t0)" -- the clause runs under the enclosing frames
  ins ("ld a0, " ++ wd 1 ++ "(t3)")
  ins "lw t5, -8(a0)" -- the call consumes the closure; the frame keeps it
  ins "bltz t5, .L_perform_call"
  ins "addiw t5, t5, 1024"
  ins "sw t5, -8(a0)"
  line ".L_perform_call:"
  ins "ld t6, 0(a0)"
  ins "jalr t6"
  ins "ld t1, 0(sp)"
  ins "la t0, _keel_handlers"
  ins "sd t1, 0(t0)"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"
  -- The machine: out and putc print, getc reads the UART; MMIO reads and writes device
  -- memory; Hart reads and sets control registers and waits for interrupts; there are no files.
  line ".L_perform_machine:"
  -- No file system: openFile, createFile and appendFile drop the path and fail; writeBytes
  -- drops its pair and fails; readByte and closeFile, which only a successful open would
  -- reach, give -1.
  forM_ [("putc", ".L_putc_op"), ("getc", ".L_getc_op"), ("read8", ".L_read8"), ("read32", ".L_read32"), ("write8", ".L_write8"), ("write32", ".L_write32"), ("csrRead", ".L_csr_read"), ("csrSet", ".L_csr_set"), ("wfi", ".L_wfi"), ("openFile", ".L_open_op"), ("createFile", ".L_open_op"), ("appendFile", ".L_open_op"), ("writeBytes", ".L_net_drop"), ("readByte", ".L_no_file"), ("closeFile", ".L_no_file")] $ \(op, l) ->
    ins ("li t0, " ++ show (opNumber op)) >> ins ("beq a0, t0, " ++ l)
  ins ("li t0, " ++ show (opNumber "tcpListen")) -- the Net operations, the last ones
  ins "bgeu a0, t0, .L_no_net"
  ins "bnez a0, .L_perform_unhandled"
  ins "mv a0, a1"
  ins "call _keel_print_i64"
  ins "li a0, 10"
  ins "call _keel_putc"
  ins "li a0, 0"
  ins "j .L_machine_ret"
  line ".L_putc_op:"
  ins "mv a0, a1"
  ins "call _keel_putc"
  ins "li a0, 0"
  ins "j .L_machine_ret"
  -- ponytail: -1 when no byte is waiting (bit 0 of the line status register), not a blocking
  -- read: QEMU's serial input has no end, so a blocking read would never see one. Block here if
  -- a console needs it.
  line ".L_getc_op:"
  unless console $ ins "li a0, -1" >> ins "j .L_machine_ret"
  ins "li t0, 0x10000000"
  ins "lbu t1, 5(t0)"
  ins "andi t1, t1, 1"
  ins "li a0, -1"
  ins "beqz t1, .L_machine_ret"
  ins "lbu a0, 0(t0)"
  ins "j .L_machine_ret"
  line ".L_open_op:"
  ins "mv a0, a1"
  ins "call _keel_drop"
  line ".L_no_file:"
  ins "li a0, -1"
  ins "j .L_machine_ret"
  -- No network: tcpListen, tcpConnect and sockSend drop the pair they were given and fail;
  -- pollWait can't wait (-2), sockRecv gives an empty array, sockClose and clockMs 0, and the
  -- rest -1.
  line ".L_no_net:"
  forM_ [("pollWait", ".L_net_nowait"), ("tcpListen", ".L_net_drop"), ("tcpConnect", ".L_net_drop"), ("sockSend", ".L_net_drop"), ("sockRecv", ".L_net_recv"), ("sockClose", ".L_net_zero"), ("clockMs", ".L_net_zero")] $ \(op, l) ->
    ins ("li t0, " ++ show (opNumber op)) >> ins ("beq a0, t0, " ++ l)
  ins "j .L_no_file"
  line ".L_net_drop:"
  ins "mv a0, a1"
  ins "call _keel_drop"
  ins "j .L_no_file"
  line ".L_net_nowait:" -- pollWait: -2, it can't wait
  ins "mv a0, a1"
  ins "call _keel_drop"
  ins "li a0, -2"
  ins "j .L_machine_ret"
  line ".L_net_recv:"
  ins "li a0, 0"
  ins "li a1, 0"
  ins "call _keel_array_alloc"
  ins "j .L_machine_ret"
  line ".L_net_zero:"
  ins "li a0, 0"
  ins "j .L_machine_ret"
  line ".L_read8:"
  ins "lbu a0, 0(a1)"
  ins "j .L_machine_ret"
  line ".L_read32:"
  ins "lwu a0, 0(a1)"
  ins "j .L_machine_ret"
  line ".L_write8:"
  ins "ld t0, 0(a1)" -- the pair's fields
  ins ("ld t1, " ++ wd 1 ++ "(a1)")
  ins "sb t1, 0(t0)"
  ins "j .L_write_done"
  line ".L_write32:"
  ins "ld t0, 0(a1)" -- the pair's fields
  ins ("ld t1, " ++ wd 1 ++ "(a1)")
  ins "sw t1, 0(t0)"
  line ".L_write_done:"
  ins "mv a0, a1" -- the (address, value) pair was passed owned
  ins "call _keel_drop"
  ins "li a0, 0"
  line ".L_machine_ret:"
  ins "ld ra, 24(sp)"
  ins "addi sp, sp, 32"
  ins "ret"
  line ".L_perform_unhandled:"
  ins "j _keel_panic_unhandled"
  -- csrRead and csrSet: a CSR's number is part of the instruction, so the ones Keel can name
  -- are dispatched here; any other panics.
  -- ponytail: four CSRs, the ones interrupt-driven firmware needs; add rows when a driver
  -- needs another.
  let csrs = [(0x300, "mstatus"), (0x304, "mie"), (0x342, "mcause"), (0x344, "mip")] :: [(Integer, String)]
  line ".L_csr_read:"
  forM_ csrs $ \(n, name) -> li "t0" n >> ins ("beq a1, t0, .L_csrr_" ++ name)
  ins "j _keel_panic_csr"
  forM_ csrs $ \(_, name) -> do
    line (".L_csrr_" ++ name ++ ":")
    ins ("csrr a0, " ++ name)
    ins "j .L_machine_ret"
  line ".L_csr_set:"
  ins "ld t0, 0(a1)" -- the pair's fields: CSR, bits
  ins ("ld t1, " ++ wd 1 ++ "(a1)")
  forM_ csrs $ \(n, name) -> li "t2" n >> ins ("beq t0, t2, .L_csrs_" ++ name)
  ins "j _keel_panic_csr"
  forM_ csrs $ \(_, name) -> do
    line (".L_csrs_" ++ name ++ ":")
    ins ("csrs " ++ name ++ ", t1")
    ins "j .L_write_done"
  line ".L_wfi:"
  ins "wfi"
  ins "li a0, 0"
  ins "j .L_machine_ret"

  -- Output through the 16550 UART: wait for bit 5 of the line status register.
  -- ponytail: the Pico 2 has no console yet (its UART needs headers and an adapter), so output
  -- goes nowhere there, and getc finds no byte.
  fn "_keel_putc"
  unless console $ ins "ret"
  ins "li t0, 0x10000000"
  line ".L_putc_wait:"
  ins "lbu t1, 5(t0)"
  ins "andi t1, t1, 0x20"
  ins "beqz t1, .L_putc_wait"
  ins "sb a0, 0(t0)"
  ins "ret"

  fn "_keel_print_str" -- a0 = NUL-terminated string
  ins "addi sp, sp, -16"
  ins "sd ra, 8(sp)"
  ins "mv a2, a0"
  line ".L_str_loop:"
  ins "lbu a0, 0(a2)"
  ins "beqz a0, .L_str_done"
  ins "call _keel_putc"
  ins "addi a2, a2, 1"
  ins "j .L_str_loop"
  line ".L_str_done:"
  ins "ld ra, 8(sp)"
  ins "addi sp, sp, 16"
  ins "ret"

  fn "_keel_print_u64" -- a0 = value, printed in decimal
  ins "addi sp, sp, -48"
  ins "sd ra, 40(sp)"
  ins "addi a2, sp, 32"
  ins "sb zero, 0(a2)"
  ins "li a3, 10"
  line ".L_u64_loop:"
  ins "remu a4, a0, a3"
  ins "divu a0, a0, a3"
  ins "addi a4, a4, 48"
  ins "addi a2, a2, -1"
  ins "sb a4, 0(a2)"
  ins "bnez a0, .L_u64_loop"
  ins "mv a0, a2"
  ins "call _keel_print_str"
  ins "ld ra, 40(sp)"
  ins "addi sp, sp, 48"
  ins "ret"

  fn "_keel_print_i64"
  ins "bgez a0, .L_i64_pos"
  ins "addi sp, sp, -16"
  ins "sd ra, 8(sp)"
  ins "sd a0, 0(sp)"
  ins "li a0, 45" -- '-'
  ins "call _keel_putc"
  ins "ld a0, 0(sp)"
  ins "neg a0, a0"
  ins "ld ra, 8(sp)"
  ins "addi sp, sp, 16"
  line ".L_i64_pos:"
  ins "tail _keel_print_u64"

  -- Exit through the virt board's test device: 0x5555 passes, (code << 16) | 0x3333 fails. The
  -- Pico 2 has none: its core sleeps, after main and after a panic alike.
  fn "_keel_exit"
  unless console $ do
    line ".L_exit_sleep:"
    ins "wfi"
    ins "j .L_exit_sleep"
  ins "li t0, 0x100000"
  ins "li t1, 0x5555"
  ins "beqz a0, .L_exit_write"
  ins "slli t1, a0, 16"
  ins "li t2, 0x3333"
  ins "or t1, t1, t2"
  line ".L_exit_write:"
  ins "sw t1, 0(t0)"
  line ".L_exit_hang:"
  ins "j .L_exit_hang"

  panic "_keel_panic_unhandled" "panic: unhandled operation\n"
  panic "_keel_panic_csr" "panic: csrRead or csrSet of a CSR other than mstatus, mie, mcause, mip\n"
  panic "_keel_panic_div" "panic: division by zero\n"
  panic "_keel_panic_bounds" "panic: array index out of bounds\n"
  panic "_keel_panic_overflow" "panic: arithmetic overflow\n"
  panic "_keel_panic_oom" "panic: out of memory\n"
  panic "_keel_panic_rc" "panic: reference count error\n"
  where
    fn lbl = line "\t.p2align 2" >> line (lbl ++ ":")
    -- Increment the statistics counter at this byte offset (uses t4–t6 only... minus the
    -- registers the caller still needs: t6 and a6 hold nothing live at these points).
    stat :: Int -> G ()
    stat off = do
      ins "la t6, _keel_stats"
      ins ("ld a6, " ++ show off ++ "(t6)")
      ins "addi a6, a6, 1"
      ins ("sd a6, " ++ show off ++ "(t6)")
    -- An array's payload words for n elements of a kind (2 + the elements, rounded up to words;
    -- on RV32 every element is a word).
    elemWords d n kind tmp = wordSize >>= \w -> if w == 4 then ins ("addi " ++ d ++ ", " ++ n ++ ", 2") else do
      ins ("snez " ++ tmp ++ ", " ++ kind)
      ins ("addi " ++ tmp ++ ", " ++ tmp ++ ", 2") -- log2 of the element size
      ins ("sll " ++ d ++ ", " ++ n ++ ", " ++ tmp)
      ins ("addi " ++ d ++ ", " ++ d ++ ", 23") -- + 7 to round up, + 16 for length and capacity
      ins ("srli " ++ d ++ ", " ++ d ++ ", 3")
    -- t3 holds a layout id from fieldLayouts on; put its pointer map in t2 (uses t4).
    pointerMap = do
      ins "la t4, _keel_layouts"
      ins ("addi t2, t3, -" ++ show fieldLayouts)
      ins "slli t2, t2, 2"
      ins "add t4, t4, t2"
      ins "lwu t2, 0(t4)"
      ins "srli t2, t2, 8"
    -- The 17-bit map in t2: its packed bit to 16(sp), t2 the map. Clobbers t5.
    splitPacked = do
      xlen <- xlenBits
      ins "srli t5, t2, 16"
      ins "sd t5, 16(sp)"
      ins ("slli t2, t2, " ++ show (xlen - 16))
      ins ("srli t2, t2, " ++ show (xlen - 16))
    -- The map of the block in a0 (header's low half in t0) into t2, its packed bit to 16(sp).
    reuseMap = do
      lMap <- newLabel
      headerMap "t2" "a0"
      ins "andi t3, t0, 0x200"
      ins ("beqz t3, " ++ lMap)
      ins "andi t3, t0, 0x3ff" -- a field in the header: the map is in the table
      pointerMap
      line (lMap ++ ":")
      splitPacked
    -- Child t4 / 8 (t4 from lowIndex) of the block in @base@ into @dst@: a word, or with the
    -- packed bit at 16(sp) a 4-byte slot holding (child - block) / 8. Clobbers t5, t6.
    child dst base = do
      lPacked <- newLabel
      lDone <- newLabel
      ins "ld t5, 16(sp)"
      ins ("bnez t5, " ++ lPacked)
      ins ("add t6, " ++ base ++ ", t4")
      ins ("ld " ++ dst ++ ", 0(t6)")
      ins ("j " ++ lDone)
      line (lPacked ++ ":")
      ins "srli t6, t4, 1"
      ins ("add t6, " ++ base ++ ", t6")
      ins ("lw " ++ dst ++ ", 0(t6)")
      ins ("slli " ++ dst ++ ", " ++ dst ++ ", 3")
      ins ("add " ++ dst ++ ", " ++ base ++ ", " ++ dst)
      line (lDone ++ ":")
    -- t3 holds a single set bit; put its byte offset (index · word size) in t4.
    lowIndex = do
      lLoop <- newLabel
      lDone <- newLabel
      w <- wordSize
      ins "li t4, 0"
      line (lLoop ++ ":")
      ins "li t5, 1"
      ins ("beq t3, t5, " ++ lDone)
      ins "srli t3, t3, 1"
      ins ("addi t4, t4, " ++ show w)
      ins ("j " ++ lLoop)
      line (lDone ++ ":")
    panic lbl msg = do
      l <- str msg
      fn lbl
      ins ("la a0, " ++ l)
      ins "call _keel_print_str"
      ins "li a0, 101"
      ins "tail _keel_exit"
