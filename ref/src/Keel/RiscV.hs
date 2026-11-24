-- | RISC-V back end (M3): the lowered IR ("Keel.Lower") → RV64IM or RV32IM assembly for a
-- freestanding target, QEMU's @virt@ board (notes.md §12, §15). Same structure and conventions
-- as "Keel.AArch64"; only the instructions and the runtime differ.
--
-- RV32 (@compileRiscVAt 32@) is the same code with 4-byte words: a block's fields, closures'
-- captured values, handler frames and array elements are 4 bytes each. A block keeps its 8-byte
-- header, so the runtime reads headers as on RV64; stack slots, the free-list table and the
-- runtime's own variables stay 8 bytes apart and use their low word. 'ins' turns the 64-bit
-- instructions into their RV32 ones.
--
-- A 64-bit integer (i64, u64; 'lWide') takes two words on RV32: in a block, Lower splits it
-- into its halves ('RJoin' joins them again); a variable lives in an 8-byte stack slot, low
-- word first. A result is a0 (low) and a1 (high). Arguments still go in a1–a7, and the high
-- half of argument k in word k of _keel_hi, which the callee reads on entry. An array of them
-- has 8-byte elements (kind 1, EWord). Multiplication, division and variable shifts are runtime
-- routines.
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
import Data.List (elemIndex, isPrefixOf)
import Data.Maybe (fromMaybe)
import Keel.Asm qualified as K
import Keel.Lower
import Keel.Runtime qualified as R
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
  case [f | fun <- lMain lp : M.elems (lFuns lp), Bind _ (RFloat (FLibm f) _) _ <- subExprs (funBody fun)] of
    f : _ -> Left ("not supported on this target: " ++ f ++ " (std.float's C library functions need a hosted target)")
    [] -> emitProgram board decls t lp

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
-- gsWide: the variables holding a 64-bit integer in two words (RV32 only).
data GS = GS {gsLabel :: Int, gsLines :: [String], gsStrings :: M.Map String String, gsNullary :: S.Set Integer, gsLayouts :: M.Map (Integer, Int, Integer) Integer, gsWord :: Int, gsBoard :: Board, gsWide :: S.Set String}

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

-- | The word's size in bytes.
wordSize :: G Int
wordSize = gets gsWord

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
emitProgram board decls mainTy (LProg funs statics mainF _ layouts consts wide) = Right (unlines (pruneRuntime (reverse (gsLines final))))
  where
    w = boardXlen board `div` 8
    final = execState gen (GS 0 [] M.empty S.empty layouts w board (if w == 4 then wide else S.empty))
    printers = printerTypes decls mainTy
    gen = do
      line "\t.section .text.start, \"ax\""
      if board == Pico2 then emitBoot else emitStart printers mainTy
      line "\t.text"
      forM_ (M.toList funs) $ \(i, f) -> emitFun ("_kf_" ++ show i) f
      emitFun "_kf_main" mainF
      emitTrap [i | (i, f) <- M.toList funs, funName f == interruptDef]
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
      line "_keel_cells:" -- one word per cell element (Keel.Syntax.cellSlots)
      mapM_ (\v -> ins ((if w == 8 then ".dword " else ".word ") ++ show v)) (cellInits decls)
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
      line "_keel_hi:" -- RV32: the high halves of 64-bit arguments, word k for argument k
      ins ".zero 32"
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
  wide <- gets gsWide
  -- A 64-bit variable on RV32 gets an 8-byte slot after the others, never a register.
  let vars = params ++ env ++ bound body
      (locs0, saved, frame0) = allocate ["s" ++ show r | r <- [1 .. 11 :: Int]] f (filter (`S.notMember` wide) vars)
      wides = S.toList (S.fromList vars `S.intersection` wide)
      locs = M.union locs0 (M.fromList (zip wides (map InSlot [frame0 `div` 8 ..])))
      frame = 16 * ((frame0 + 8 * length wides + 15) `div` 16)
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
  offs <- wordOffsets base env
  forM_ (zip offs env) $ \(j, v) -> do
    ins ("ld t0, " ++ show (w * j) ++ "(a0)")
    store slots "t0" v
    whenWide v $ ins ("lw t0, " ++ show (w * (j + 1)) ++ "(a0)") >> storeHi slots "t0" v
  line ("L" ++ lbl ++ "_loop:")
  forM_ (zip [1 :: Int ..] params) $ \(r, p) -> do
    store slots ("a" ++ show r) p
    whenWide p $ ins "la t6, _keel_hi" >> ins ("lw t5, " ++ show (4 * r) ++ "(t6)") >> storeHi slots "t5" p
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

-- RV32's 64-bit variables ----------------------------------------------------------------

whenWide :: String -> G () -> G ()
whenWide v g = gets (S.member v . gsWide) >>= \yes -> when yes g

-- | Whether an atom may be a 64-bit value on RV32: a 64-bit variable, or a constant (which
-- could be one; its high half costs an instruction).
mayBeWide :: Atom -> G Bool
mayBeWide a = case a of
  AVar v -> gets (S.member v . gsWide)
  AInt _ -> (== 4) <$> wordSize
  _ -> pure False

-- | The word offsets of a block's values from @base@: a 64-bit variable takes two on RV32.
wordOffsets :: Int -> [String] -> G [Int]
wordOffsets base vs = do
  wide <- gets gsWide
  pure (scanl (\j v -> j + if v `S.member` wide then 2 else 1) base vs)

-- | A 64-bit variable's high half (the second word of its slot).
storeHi, loadHi :: Slots -> String -> String -> G ()
storeHi slots r v = case fLocs slots M.! v of
  InSlot i -> slot (8 * i + 4) >>= \s' -> ins ("sw " ++ r ++ ", " ++ s')
  InReg _ -> error ("storeHi: " ++ v ++ " is in a register")
loadHi slots r v = case fLocs slots M.! v of
  InSlot i -> slot (8 * i + 4) >>= \s' -> ins ("lw " ++ r ++ ", " ++ s')
  InReg _ -> error ("loadHi: " ++ v ++ " is in a register")

-- | An atom's high half into r (RV32): a 64-bit variable's, a constant's, else the sign of a
-- narrow value (so widening is this and the value itself).
atomHi :: Slots -> String -> Atom -> G ()
atomHi slots r a = case a of
  AInt n -> li r (n `div` (2 ^ (32 :: Int)))
  AVar v -> gets (S.member v . gsWide) >>= \yes ->
    if yes then loadHi slots r v else load' slots r v >> ins ("srai " ++ r ++ ", " ++ r ++ ", 31")
  _ -> li r 0

-- | A value into a0, and its high half into a1 when it may be 64 bits on RV32.
atomRes :: Slots -> Atom -> G ()
atomRes slots a = do
  atom slots "a0" a
  wideish <- mayBeWide a
  when wideish $ atomHi slots "a1" a

-- | Store a result (a0, and a1 for a 64-bit variable on RV32) to a variable.
storeRes :: Slots -> String -> G ()
storeRes slots x = store slots "a0" x >> whenWide x (storeHi slots "a1" x)

-- | Argument k into register ak, its high half into _keel_hi when it may be 64 bits on RV32.
arg :: Slots -> Int -> Atom -> G ()
arg slots k a = do
  atom slots ("a" ++ show k) a
  wideish <- mayBeWide a
  when wideish $ do
    atomHi slots "t5" a
    ins "la t6, _keel_hi"
    ins ("sw t5, " ++ show (4 * k) ++ "(t6)")

-- | Panic (out of bounds) unless an index's or a length's high half is 0 (RV32).
hiZero :: Slots -> Atom -> G ()
hiZero slots a = do
  wideish <- mayBeWide a
  when wideish $ atomHi slots "t5" a >> jumpIf "bnez" ["t5"] "_keel_panic_bounds"

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
    atomRes slots a
    case join of
      Nothing -> leave slots >> ins "ret"
      Just (v, lbl) -> storeRes slots v >> ins ("j " ++ lbl)
  Bind x rhs (Ret (AVar y)) | x == y, Nothing <- join, Just tc <- tailCall rhs -> tc
  Bind x rhs rest -> do
    rhsCode slots rhs
    storeRes slots x
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
  Drop v 0 rest -> do
    load' slots "a0" v
    ins "call _keel_drop"
    expr slots join rest
  Drop v mask rest -> do
    load' slots "a0" v
    li "a1" mask
    ins "call _keel_drop_fields"
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
        arg slots 1 a
        ins "ld t6, 0(a0)"
        leave slots
        ins "jr t6"
      RCallKnown i as -> Just $ do
        forM_ (zip [1 :: Int ..] as) $ uncurry (arg slots)
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

-- | Arithmetic or a comparison on operands that fit a register (t0, t1), into a0.
prim64 :: Slots -> Prim -> IntTy -> Atom -> Atom -> G ()
prim64 slots op it a b = do
  atom slots "t0" a
  atom slots "t1" b
  case op of
    Eq -> ins "xor a0, t0, t1" >> ins "seqz a0, a0"
    Lt -> ins ((if signed it then "slt" else "sltu") ++ " a0, t0, t1")
    Arith _ aop | aop `elem` [Div, Rem] -> divide it aop
    Arith ov aop -> arith it ov aop
    Bits bop -> bitwise it bop

-- | The same on 64-bit operands on RV32: a in (t0, t1), b in (t2, t3), low half first; a
-- 64-bit result in (a0, a1).
primWide :: Slots -> Prim -> IntTy -> Atom -> Atom -> G ()
primWide slots op it@(IntTy sgn _) a b = do
  atom slots "t0" a
  atomHi slots "t1" a
  atom slots "t2" b
  atomHi slots "t3" b
  case op of
    Eq -> mapM_ ins ["xor a0, t0, t2", "xor a1, t1, t3", "or a0, a0, a1", "seqz a0, a0"]
    Lt -> do
      lDone <- newLabel
      ins ((if sgn then "slt" else "sltu") ++ " a0, t1, t3")
      ins ("bne t1, t3, " ++ lDone)
      ins "sltu a0, t0, t2"
      line (lDone ++ ":")
    Arith _ aop | aop `elem` [Div, Rem] -> do
      ins "or a2, t2, t3"
      jumpIf "beqz" ["a2"] "_keel_panic_div"
      when (sgn && aop == Div) $ do -- the minimum / -1
        lOk <- newLabel
        ins "li a2, -1"
        ins ("bne t2, a2, " ++ lOk)
        ins ("bne t3, a2, " ++ lOk)
        ins ("bnez t0, " ++ lOk)
        li "a2" 0x80000000
        jumpIf "beq" ["t1", "a2"] "_keel_panic_overflow"
        line (lOk ++ ":")
      operands
      ins (if sgn then "call _keel_sdivmod64" else "call _keel_udivmod64")
      when (aop == Rem) $ ins "mv a0, a2" >> ins "mv a1, a3"
    Arith ov aop -> arithWide it ov aop
    Bits bop -> case bop of
      And -> ins "and a0, t0, t2" >> ins "and a1, t1, t3"
      Or -> ins "or a0, t0, t2" >> ins "or a1, t1, t3"
      Xor -> ins "xor a0, t0, t2" >> ins "xor a1, t1, t3"
      _ -> case b of
        AInt k -> shiftBy bop (if sgn && k < 0 then 0 else k)
        _ -> shiftVar bop
  where
    operands = mapM_ ins ["mv a0, t0", "mv a1, t1", "mv a2, t2", "mv a3, t3"]
    -- As on RV64: a negative amount (signed) shifts by 0, one beyond 63 shifts everything out.
    shiftBy bop k
      | k == 0 = ins "mv a0, t0" >> ins "mv a1, t1"
      | k > 63 = out
      | bop == Shl, k < 32 = mapM_ ins ["slli a1, t1, " ++ show k, "srli a2, t0, " ++ show (32 - k), "or a1, a1, a2", "slli a0, t0, " ++ show k]
      | bop == Shl = ins ("slli a1, t0, " ++ show (k - 32)) >> ins "li a0, 0"
      | k < 32 = mapM_ ins ["srli a0, t0, " ++ show k, "slli a2, t1, " ++ show (32 - k), "or a0, a0, a2", right ++ " a1, t1, " ++ show k]
      | otherwise = ins (right ++ " a0, t1, " ++ show (k - 32)) >> fill
    right = if sgn then "srai" else "srli"
    fill = if sgn then ins "srai a1, t1, 31" else ins "li a1, 0"
    out = case op of
      Bits Shl -> ins "li a0, 0" >> ins "li a1, 0"
      _ -> fill >> ins "mv a0, a1"
    shiftVar bop = do
      lPos <- newLabel
      lBig <- newLabel
      lDone <- newLabel
      when sgn $ do
        ins ("bgez t3, " ++ lPos)
        ins "li t2, 0"
        ins "li t3, 0"
      line (lPos ++ ":")
      ins ("bnez t3, " ++ lBig)
      ins "li a2, 63"
      ins ("bgtu t2, a2, " ++ lBig)
      ins "mv a0, t0"
      ins "mv a1, t1"
      ins "mv a2, t2"
      ins (case bop of Shl -> "call _keel_shl64"; _ | sgn -> "call _keel_sra64"; _ -> "call _keel_shr64")
      ins ("j " ++ lDone)
      line (lBig ++ ":")
      out
      line (lDone ++ ":")

-- | Add, subtract or multiply 64-bit operands on RV32, (t0, t1) and (t2, t3), into (a0, a1),
-- in an overflow mode (as 'arith').
arithWide :: IntTy -> Overflow -> ArithOp -> G ()
arithWide it@(IntTy sgn _) ov aop = do
  lOvf <- if ov == Checked then pure "_keel_panic_overflow" else newLabel
  case aop of
    Add -> do
      mapM_ ins ["add a0, t0, t2", "sltu a2, a0, t0", "add a1, t1, t3", "add a1, a1, a2"]
      unless (ov == Wrap) $
        if sgn
          then mapM_ ins ["xor a2, t1, a1", "xor a3, t3, a1", "and a2, a2, a3"] >> jumpIf "bltz" ["a2"] lOvf
          else below "a1" "a0" "t1" "t0" lOvf -- the sum below an operand: it carried out
    Sub -> do
      unless (ov == Wrap || sgn) $ below "t1" "t0" "t3" "t2" lOvf
      mapM_ ins ["sltu a2, t0, t2", "sub a0, t0, t2", "sub a1, t1, t3", "sub a1, a1, a2"]
      when (ov /= Wrap && sgn) $
        mapM_ ins ["xor a2, t1, t3", "xor a3, t1, a1", "and a2, a2, a3"] >> jumpIf "bltz" ["a2"] lOvf
    _ -> do
      mapM_ ins ["mv a0, t0", "mv a1, t1", "mv a2, t2", "mv a3, t3"]
      ins (if sgn && ov /= Wrap then "call _keel_muls64" else "call _keel_mulu64") -- keep t1, t3
      unless (ov == Wrap) $ jumpIf "bnez" ["a2"] lOvf
  case ov of
    Saturate -> do
      lDone <- newLabel
      ins ("j " ++ lDone)
      line (lOvf ++ ":")
      if not sgn
        then if aop == Sub then ins "li a0, 0" >> ins "li a1, 0" else ins "li a0, -1" >> ins "li a1, -1"
        else do
          lEnd <- newLabel
          if aop == Mul then ins "xor t4, t1, t3" else ins "mv t4, t1"
          ins "li a0, -1"
          li "a1" 0x7fffffff
          ins ("bgez t4, " ++ lEnd)
          ins "li a0, 0"
          li "a1" 0x80000000
          line (lEnd ++ ":")
      line (lDone ++ ":")
    Optional -> do
      lDone <- newLabel
      (none, some) <- gets (\st -> optionLayouts (gsLayouts st) it)
      -- Some's low half is in the header, its high half its word.
      ins "mv t2, a0"
      ins "mv t3, a1"
      alloc 1 some
      ins "sw t2, -4(a0)"
      ins "sw t3, 0(a0)"
      ins ("j " ++ lDone)
      line (lOvf ++ ":")
      atom (Slots M.empty [] Nothing) "a0" (ANullary none)
      line (lDone ++ ":")
    _ -> pure ()
  where
    -- Jump to l when (xh, xl) < (yh, yl), unsigned.
    below xh xl yh yl l = do
      lNo <- newLabel
      jumpIf "bltu" [xh, yh] l
      ins ("bne " ++ xh ++ ", " ++ yh ++ ", " ++ lNo)
      jumpIf "bltu" [xl, yl] l
      line (lNo ++ ":")

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
  RAtom a -> atomRes slots a
  RJoin lo hi -> atom slots "a0" lo >> atom slots "a1" hi
  RCell k v -> do
    w <- wordSize
    atom slots "t0" k
    ins ("slli t0, t0, " ++ (if w == 8 then "3" else "2"))
    ins "la t1, _keel_cells"
    ins "add t0, t0, t1"
    case v of
      Nothing -> ins "ld a0, 0(t0)"
      Just a -> atom slots "t2" a >> ins "sd t2, 0(t0)" >> ins "li a0, 0"
  RPrim op it a b | bits it == 64 -> wordSize >>= \w -> if w == 4 then primWide slots op it a b else prim64 slots op it a b
  RPrim op it a b -> prim64 slots op it a b
  RCall f a -> do
    atom slots "a0" f
    arg slots 1 a
    ins "ld t6, 0(a0)"
    ins "jalr t6"
  RCallKnown i as -> do
    forM_ (zip [1 :: Int ..] as) $ uncurry (arg slots)
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
    arg slots 1 a
    li "a0" (toInteger n)
    ins "call _keel_perform"
  -- write8(a, v) and the like: the machine takes the two words in registers; only a handler
  -- that takes the operation gets them as a pair.
  RPerform2 n lid a b -> do
    lMachine <- newLabel
    lDone <- newLabel
    li "a0" (toInteger n)
    ins "call _keel_handled"
    jumpIf "beqz" ["a0"] lMachine
    rhsCode slots (RAlloc lid Nothing [a, b])
    ins "mv a1, a0"
    li "a0" (toInteger n)
    ins "call _keel_perform"
    ins ("j " ++ lDone)
    line (lMachine ++ ":")
    atom slots "a1" a
    atom slots "a2" b
    li "a0" (toInteger n)
    ins "call _keel_machine2"
    line (lDone ++ ":")
  -- On RV32 a 64-bit result is the value and its high half (a narrow value's sign, or the
  -- high half it had); a narrow one is the low word, re-extended.
  RConv to a | bits to == 64 -> wordSize >>= \w -> atom slots "a0" a >> when (w == 4) (atomHi slots "a1" a)
  RConv to a -> atom slots "a0" a >> canonical to
  -- f64 (RV64 only) lives in integer registers as its bits; ft0 and ft1 hold it for the
  -- operation (the trap handler saves them).
  RFPrim op a b -> do
    atom slots "t0" a
    atom slots "t1" b
    ins "fmv.d.x ft0, t0"
    ins "fmv.d.x ft1, t1"
    case op of
      Eq -> ins "feq.d a0, ft0, ft1"
      Lt -> ins "flt.d a0, ft0, ft1"
      Arith _ aop -> do
        ins ((case aop of Add -> "fadd.d"; Sub -> "fsub.d"; Mul -> "fmul.d"; _ -> "fdiv.d") ++ " ft0, ft0, ft1")
        ins "fmv.x.d a0, ft0"
      _ -> error "float primitive"
  RFOfInt it a -> do
    atom slots "t0" a
    ins ((if signed it then "fcvt.d.l" else "fcvt.d.lu") ++ " ft0, t0")
    ins "fmv.x.d a0, ft0"
  RFloat op as -> do
    forM_ (zip ["t0", "t1"] as) $ \(r, a) -> atom slots r a
    ins "fmv.d.x ft0, t0"
    case op of
      -- fcvt saturates to 64 bits but gives the maximum for NaN: NaN is 0 here, as elsewhere;
      -- narrower types clamp on.
      FToInt it@(IntTy sgn n) -> do
        lNum <- newLabel
        ins ((if sgn then "fcvt.l.d" else "fcvt.lu.d") ++ " a0, ft0, rtz")
        ins "feq.d t1, ft0, ft0"
        ins ("bnez t1, " ++ lNum)
        ins "li a0, 0"
        line (lNum ++ ":")
        when (n < 64) $ do
          let (lo, hi) = intRange it
          lHi <- newLabel
          li "t1" hi
          ins ((if sgn then "bge" else "bgeu") ++ " t1, a0, " ++ lHi)
          ins "mv a0, t1"
          line (lHi ++ ":")
          when sgn $ do
            lLo <- newLabel
            li "t1" lo
            ins ("bge a0, t1, " ++ lLo)
            ins "mv a0, t1"
            line (lLo ++ ":")
      FGe -> ins "fmv.d.x ft1, t1" >> ins "fle.d a0, ft1, ft0"
      FSqrt -> ins "fsqrt.d ft0, ft0" >> ins "fmv.x.d a0, ft0"
      _ -> error ("float operation " ++ show op ++ " has no RISC-V code")
  -- Arrays: as in "Keel.AArch64".
  RArena True -> ins "call _keel_arena_open"
  RArena False -> ins "call _keel_arena_close"
  RArray ALength _ [a] -> atom slots "t0" a >> ins "ld a0, 0(t0)" >> wordSize >>= \w -> when (w == 4) (ins "li a1, 0")
  RArray AGet e [a, i] -> do
    hiZero slots i
    atom slots "t0" a
    atom slots "t1" i
    ins "ld t2, 0(t0)"
    jumpIf "bgeu" ["t1", "t2"] "_keel_panic_bounds" -- unsigned: a negative index is out of bounds too
    element e
  RIndex a i e -> atom slots "t0" a >> atom slots "t1" i >> element e
  RArray op e as -> do
    forM_ (zip [0 :: Int ..] as) $ \(r, a) -> atom slots ("a" ++ show r) a
    -- RV32: an index or a length is 64 bits (its high half must be 0), and an 8-byte element's
    -- high half goes in the next register after the arguments.
    w <- wordSize
    when (w == 4) $ do
      case (op, as) of
        (ANew, n : _) -> hiZero slots n
        (ASet, [_, i, _]) -> hiZero slots i
        _ -> pure ()
      when (e == EWord && op `elem` [ANew, ASet, APush]) $ do
        let r = if op == ANew then 3 else length as
        atomHi slots ("a" ++ show r) (last as)
    case op of
      AEmpty -> li "a0" 0 >> li "a1" (elemKind e) >> ins "call _keel_array_alloc"
      ANew -> li "a2" (elemKind e) >> ins "call _keel_array_new"
      ASet -> ins "call _keel_array_set"
      APush -> ins "call _keel_array_push"
      _ -> ins "call _keel_array_pop"
  where
    storeAll :: Int -> [String] -> G ()
    storeAll from vs = do
      w <- wordSize
      offs <- wordOffsets from vs
      forM_ (zip offs vs) $ \(j, v) -> do
        load' slots "t2" v
        ins ("sd t2, " ++ show (w * j) ++ "(a0)")
        whenWide v $ loadHi slots "t2" v >> ins ("sw t2, " ++ show (w * (j + 1)) ++ "(a0)")
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

-- | Load element t1 of array t0 into a0. Elements follow the length and the capacity. On RV32
-- a pointer is 4 bytes, and a word element (a 64-bit integer) 8: its high half into a1.
element :: Elem -> G ()
element e = do
  w <- wordSize
  ins ("slli t1, t1, " ++ (case e of ENarrow _ -> "2"; EPtr | w == 4 -> "2"; _ -> "3"))
  ins "add t0, t0, t1"
  ins ((case e of ENarrow True -> "lw"; ENarrow False -> "lwu"; _ -> "ld") ++ " a0, " ++ show (2 * w) ++ "(t0)")
  when (w == 4 && e == EWord) $ ins "lw a1, 12(t0)"

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
  w <- wordSize
  let phys = physicalIndices (8 * w)
  case t of
    TInt (IntTy sgn n) -> ins ("call _keel_print_" ++ (if sgn then "i64" else "u64") ++ (if w == 4 && n == 64 then "w" else ""))
    TFloat -> ins "call _keel_print_x64" -- its IEEE bits, as the evaluator shows it
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
    TBox a -> printStr "box " >> field [Right (-1, False)] a
    TPair a b -> do
      let (pa, pb) = case phys [a, b] of
            [x, y] -> (x, y)
            _ -> ([0], [1])
      printStr "("
      field [Right (i, False) | i <- pa] a
      printStr ", "
      field [Right (i, False) | i <- pb] b
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
          forM_ (zip3 [0 :: Int ..] fts (phys fts)) $ \(k, ft, is) -> do
            when (k > 0) $ printStr ", "
            let place i =
                  let j = fromMaybe i (elemIndex i ws)
                      rel = case keyOf layouts lid of
                        Just (_, _, bm) | Just nw <- packedFrom bm (length ws), j >= nw -> Just (nw + j)
                        _ -> Nothing
                   in if h == Just i then Left (case ft of TInt it -> signed it && length is == 1; _ -> False) else Right (maybe (j, False) (,True) rel)
            field (map place is) ft
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
    -- header field (Left: whether signed); a 64-bit value on RV32 is two such places, its
    -- high half into a1.
    field :: [Either Bool (Int, Bool)] -> Ty -> G ()
    field places ft = do
      ins "ld a0, 0(sp)"
      case places of
        [lo, hi] -> fetch "a1" hi >> fetch "a0" lo
        _ -> mapM_ (fetch "a0") places
      case M.lookup (prettyTy ft) printers of
        Just (_, l) -> ins ("call " ++ l)
        Nothing -> printStr "..."
    -- From the block in a0.
    fetch d place = case place of
      Left sgn -> ins ((if sgn then "lw" else "lwu") ++ " " ++ d ++ ", -4(a0)")
      Right (i, True) -> ins ("lw t0, " ++ show (4 * i) ++ "(a0)") >> ins "slli t0, t0, 3" >> ins ("add " ++ d ++ ", a0, t0")
      Right (i, _) -> when (i >= 0) $ wordSize >>= \w -> ins ("ld " ++ d ++ ", " ++ show (w * i) ++ "(a0)")

-- | The words of a block holding values of these types, for each, at this word size in bits:
-- one each, except a 64-bit integer on a 32-bit target, two.
physicalIndices :: Int -> [Ty] -> [[Int]]
physicalIndices word ts = [[j .. j + n - 1] | (j, n) <- zip (scanl (+) 0 sizes) sizes]
  where
    sizes = map (length . physical word . pure) ts

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
  ins "la t0, _keel_trap"
  ins "csrw mtvec, t0"
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

-- | mtvec's target. With @def interrupt@, an interrupt (mcause's top bit) saves what the
-- interrupted code may hold in caller-saved registers and in the runtime's globals, calls it
-- with mcause and returns with mret; every other trap, and every trap without it, panics.
-- The handler runs on the interrupted stack, with no handler frames (its operations reach the
-- machine), and interrupts stay off until mret (the hart clears mstatus.MIE on entry).
-- ponytail: one handler for every interrupt, not nested; vectored mode when latency matters.
emitTrap :: [Int] -> G ()
emitTrap handler = do
  w <- wordSize
  line "\t.p2align 2"
  line "_keel_trap:"
  case handler of
    [i] -> do
      let regs = "ra" : ["t" ++ show k | k <- [0 .. 6 :: Int]] ++ ["a" ++ show k | k <- [0 .. 7 :: Int]]
          hiWords = 32 `div` w -- _keel_hi's size
          fregs = if w == 8 then ["ft0", "ft1"] else [] -- f64 operands (RV64 only, with the FPU on)
          fat k = show ((length regs + 1 + hiWords + k) * w) ++ "(sp)"
          frame = 16 * (((length regs + 1 + hiWords + length fregs) * w + 15) `div` 16)
          at k = show (k * w) ++ "(sp)"
      ins ("addi sp, sp, -" ++ show frame)
      forM_ (zip [0 ..] regs) $ \(k, r) -> ins ("sd " ++ r ++ ", " ++ at k)
      forM_ (zip [0 ..] fregs) $ \(k, r) -> ins ("fsd " ++ r ++ ", " ++ fat k)
      ins "csrr a1, mcause"
      ins "bgez a1, _keel_trap_fatal" -- an exception: mret would run the faulting instruction again
      let globals = (length regs, "_keel_handlers") : [(length regs + 1 + k, "_keel_hi+" ++ show (k * w)) | k <- [0 .. hiWords - 1]]
      forM_ globals $ \(k, g) -> ins ("la t0, " ++ g) >> ins "ld t1, 0(t0)" >> ins ("sd t1, " ++ at k)
      ins "la t0, _keel_handlers"
      ins "sd zero, 0(t0)"
      ins ("call _kf_" ++ show i)
      forM_ globals $ \(k, g) -> ins ("ld t1, " ++ at k) >> ins ("la t0, " ++ g) >> ins "sd t1, 0(t0)"
      forM_ (zip [0 ..] regs) $ \(k, r) -> ins ("ld " ++ r ++ ", " ++ at k)
      forM_ (zip [0 ..] fregs) $ \(k, r) -> ins ("fld " ++ r ++ ", " ++ fat k)
      ins ("addi sp, sp, " ++ show frame)
      ins "mret"
    _ -> ins "j _keel_trap_fatal"

-- | Entry point: set up the stack, run main, print the result and the allocator counters
-- (always: there is no environment to ask), then exit through the test device.
emitStart :: M.Map String (Ty, String) -> Ty -> G ()
emitStart printers t = do
  line "\t.globl _start"
  line "\t.p2align 2"
  line "_start:"
  ins "la sp, _keel_stack_top"
  ins "la t0, _keel_trap"
  ins "csrw mtvec, t0"
  rv64 <- (== 8) <$> wordSize
  when rv64 $ ins "li t0, 0x2000" >> ins "csrs mstatus, t0" -- mstatus.FS = Initial: the FPU on
  ins "li a0, 0"
  ins "call _kf_main"
  ins "addi sp, sp, -16"
  ins "sd a0, 0(sp)"
  rv32 <- (== 4) <$> wordSize
  when rv32 $ ins "sw a1, 8(sp)" -- a 64-bit result's high half
  printStr "result: "
  ins "ld a0, 0(sp)"
  when rv32 $ ins "lw a1, 8(sp)"
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

-- | The portable assembler ("Keel.Asm") for the shared runtime, for words of @w@ bytes. A =
-- a0–a2; T = t4–t6, a6 (what the allocator may clobber), then t0–t3. Instructions are written
-- for RV64; 'ins' turns them into RV32 ones.
asmRv :: Int -> K.Asm G
asmRv w =
  K.Asm
    { K.wordBytes = w
    , K.mov = \d o -> case o of
        K.R s -> ins ("mv " ++ r d ++ ", " ++ r s)
        K.I n -> li (r d) n
    , K.op = \o d a b -> case b of
        K.R s -> ins (opName o ++ " " ++ r d ++ ", " ++ r a ++ ", " ++ r s)
        K.I n | o == K.Sub -> ins ("addi " ++ r d ++ ", " ++ r a ++ ", " ++ show (negate n))
        K.I n -> ins (opName o ++ "i " ++ r d ++ ", " ++ r a ++ ", " ++ show n)
    , K.load = \wd d b off -> ins (loadName wd ++ " " ++ r d ++ ", " ++ show off ++ "(" ++ r b ++ ")")
    , K.store = \wd v b off -> ins (storeName wd ++ " " ++ r v ++ ", " ++ show off ++ "(" ++ r b ++ ")")
    , K.loadIx = \d b i k -> do
        when (d == b) $ error "asmRv: loadIx into its base"
        ins ("slli " ++ r d ++ ", " ++ r i ++ ", " ++ show k)
        ins ("add " ++ r d ++ ", " ++ r b ++ ", " ++ r d)
        ins ("ld " ++ r d ++ ", 0(" ++ r d ++ ")")
    , K.storeIx = \v b i k t -> do
        ins ("slli " ++ r t ++ ", " ++ r i ++ ", " ++ show k)
        ins ("add " ++ r t ++ ", " ++ r b ++ ", " ++ r t)
        ins ("sd " ++ r v ++ ", 0(" ++ r t ++ ")")
    , K.addScaled = \d a b k -> do
        when (d == a) $ error "asmRv: addScaled into its first operand"
        ins ("slli " ++ r d ++ ", " ++ r b ++ ", " ++ show k)
        ins ("add " ++ r d ++ ", " ++ r a ++ ", " ++ r d)
    , K.branch = \c a o l -> do
        let b = case o of
              K.R s -> r s
              K.I 0 -> "zero"
              K.I n -> error ("asmRv: compare with " ++ show n ++ ": move it into a register")
            mnemonic = "b" ++ cond c
        if ".L" `isPrefixOf` l then ins (mnemonic ++ " " ++ r a ++ ", " ++ b ++ ", " ++ l) else jumpIf mnemonic [r a, b] l
    , K.branchBit = \set n a t l ->
        if n < 11
          then do
            ins ("andi " ++ r t ++ ", " ++ r a ++ ", " ++ show (2 ^ n :: Integer))
            ins ((if set then "bnez " else "beqz ") ++ r t ++ ", " ++ l)
          else do
            ins ("slli " ++ r t ++ ", " ++ r a ++ ", " ++ show (8 * w - 1 - n))
            ins ((if set then "bltz " else "bgez ") ++ r t ++ ", " ++ l)
    , -- No Zbb (rv64imafdc, rv32imac): isolate the lowest bit and count the shifts.
      K.lowBit = \d s t -> do
        lLoop <- newLabel
        lDone <- newLabel
        ins ("neg " ++ r t ++ ", " ++ r s)
        ins ("and " ++ r t ++ ", " ++ r s ++ ", " ++ r t)
        ins ("li " ++ r d ++ ", 0")
        line (lLoop ++ ":")
        ins ("srli " ++ r t ++ ", " ++ r t ++ ", 1")
        ins ("beqz " ++ r t ++ ", " ++ lDone)
        ins ("addi " ++ r d ++ ", " ++ r d ++ ", 1")
        ins ("j " ++ lLoop)
        line (lDone ++ ":")
    , K.jump = \l -> ins ("j " ++ l)
    , K.call = \l -> ins ("call " ++ l)
    , K.callReg = \a -> ins ("jalr " ++ r a)
    , K.ret = ins "ret"
    , K.addr = \d sym -> ins ("la " ++ r d ++ ", " ++ sym)
    , K.loadSym = \d sym -> ins ("la " ++ r d ++ ", " ++ sym) >> ins ("ld " ++ r d ++ ", 0(" ++ r d ++ ")")
    , K.stat = \off t1 t2 -> do
        ins ("la " ++ r t1 ++ ", _keel_stats")
        ins ("ld " ++ r t2 ++ ", " ++ show off ++ "(" ++ r t1 ++ ")")
        ins ("addi " ++ r t2 ++ ", " ++ r t2 ++ ", 1")
        ins ("sd " ++ r t2 ++ ", " ++ show off ++ "(" ++ r t1 ++ ")")
    , K.frame = \n -> ins ("addi sp, sp, -" ++ show (frameSize n)) >> ins ("sd ra, " ++ show (frameSize n - 8) ++ "(sp)")
    , K.unframe = \n -> ins ("ld ra, " ++ show (frameSize n - 8) ++ "(sp)") >> ins ("addi sp, sp, " ++ show (frameSize n))
    , K.slot = (8 *)
    , K.fn = \l -> line "\t.p2align 2" >> line (l ++ ":")
    , K.label = \l -> line (l ++ ":")
    , K.local = (".L_" ++)
    , K.newLabel = newLabel
    }
  where
    r a = case a of
      K.A i -> "a" ++ show i
      K.T i -> ["t4", "t5", "t6", "a6", "t0", "t1", "t2", "t3"] !! i
      K.Sp -> "sp"
    loadName wd = case wd of
      K.Byte -> "lbu"
      K.Half32 True -> "lw"
      K.Half32 False -> "lwu"
      K.Word -> "ld"
    storeName wd = case wd of
      K.Byte -> "sb"
      K.Half32 _ -> "sw"
      K.Word -> "sd"
    opName o = case o of
      K.Add -> "add"
      K.Sub -> "sub"
      K.And -> "and"
      K.Or -> "or"
      K.Xor -> "xor"
      K.Shl -> "sll"
      K.Shr -> "srl"
      K.Sar -> "sra"
    cond c = case c of
      K.Eq -> "eq"
      K.Ne -> "ne"
      K.Ltu -> "ltu"
      K.Geu -> "geu"
      K.Gtu -> "gtu"
      K.Leu -> "leu"
      K.Lts -> "lt"
      K.Ges -> "ge"
    frameSize n = 16 * ((8 * n + 8 + 15) `div` 16)

emitRuntime :: G ()
emitRuntime = do
  w <- wordSize
  console <- gets ((/= Pico2) . gsBoard)
  let wd k = show (k * w) -- the byte offset of word k
      rv32 = w == 4
  R.alloc (asmRv w) (toInteger maxSmall)
  R.arenaOpen (asmRv w)
  R.arenaClose (asmRv w)

  R.dropBlock (asmRv w)
  R.dropFields (asmRv w)
  R.freeBlock (asmRv w) (toInteger maxSmall)

  R.arrays (asmRv w)

  R.dropReuse (asmRv w)

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
  if rv32
    then ins "la t0, _keel_hi" >> ins "lw a1, 4(t0)" >> ins "call _keel_print_i64w"
    else ins "call _keel_print_i64"
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
  when rv32 $ ins "srai a1, a0, 31" -- a 64-bit result's high half: they are all small
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

  -- _keel_handled: a0 = operation number → a0 = 1 if a handler frame takes it, else 0.
  -- Clobbers t1–t4.
  fn "_keel_handled"
  ins "la t1, _keel_handlers"
  ins "ld t1, 0(t1)"
  line ".L_handled_frame:"
  ins "beqz t1, .L_handled_no"
  ins ("ld t2, " ++ wd 1 ++ "(t1)")
  ins ("addi t3, t1, " ++ wd 2)
  line ".L_handled_scan:"
  ins "beqz t2, .L_handled_next"
  ins "ld t4, 0(t3)"
  ins "beq t4, a0, .L_handled_yes"
  ins ("addi t3, t3, " ++ wd 2)
  ins "addi t2, t2, -1"
  ins "j .L_handled_scan"
  line ".L_handled_next:"
  ins "ld t1, 0(t1)"
  ins "j .L_handled_frame"
  line ".L_handled_yes:"
  ins "li a0, 1"
  ins "ret"
  line ".L_handled_no:"
  ins "li a0, 0"
  ins "ret"

  -- _keel_machine2: a0 = write8, write32 or csrSet, a1 and a2 = its two words → a0 = 0.
  fn "_keel_machine2"
  ins ("li t0, " ++ show (opNumber "write8"))
  ins "beq a0, t0, .L_m2_write8"
  ins ("li t0, " ++ show (opNumber "write32"))
  ins "beq a0, t0, .L_m2_write32"
  forM_ csrs $ \(n, name) -> li "t2" n >> ins ("beq a1, t2, .L_m2_csrs_" ++ name)
  ins "j _keel_panic_csr"
  forM_ csrs $ \(_, name) -> do
    line (".L_m2_csrs_" ++ name ++ ":")
    ins ("csrs " ++ name ++ ", a2")
    ins "j .L_m2_done"
  line ".L_m2_write8:"
  ins "sb a2, 0(a1)"
  ins "j .L_m2_done"
  line ".L_m2_write32:"
  ins "sw a2, 0(a1)"
  line ".L_m2_done:"
  ins "li a0, 0"
  ins "li a1, 0"
  ins "ret"

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

  fn "_keel_print_x64" -- a0 = value, printed as 0x and hex digits (RV64)
  ins "addi sp, sp, -48"
  ins "sd ra, 40(sp)"
  ins "addi a2, sp, 32"
  ins "sb zero, 0(a2)"
  line ".L_x64_loop:"
  ins "andi a4, a0, 15"
  ins "srli a0, a0, 4"
  ins "addi a4, a4, 48"
  ins "li a3, 58"
  ins "blt a4, a3, .L_x64_digit"
  ins "addi a4, a4, 39" -- past '9': a–f
  line ".L_x64_digit:"
  ins "addi a2, a2, -1"
  ins "sb a4, 0(a2)"
  ins "bnez a0, .L_x64_loop"
  ins "li a4, 120" -- 'x'
  ins "sb a4, -1(a2)"
  ins "li a4, 48" -- '0'
  ins "sb a4, -2(a2)"
  ins "addi a0, a2, -2"
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

  when rv32 wideRuntime

  -- A fatal trap: a fault (illegal instruction, bad address, ecall), or an interrupt with no
  -- def interrupt. The stack pointer may be what faulted, so start a fresh stack.
  -- 'emitTrap' comes here for every trap without a handler.
  fn "_keel_trap_fatal"
  ins "la sp, _keel_stack_top"
  forM_ [("panic: trap mcause=", "mcause"), (" mepc=", "mepc"), (" mtval=", "mtval")] $ \(label, csr) -> do
    printStr label
    ins ("csrr a0, " ++ csr)
    ins "call _keel_print_hex"
  printStr "\n"
  ins "li a0, 101"
  ins "tail _keel_exit"

  fn "_keel_print_hex" -- a0 = value, printed as 0x and hex digits
  ins "addi sp, sp, -48"
  ins "sd ra, 40(sp)"
  ins "addi a2, sp, 32"
  ins "sb zero, 0(a2)"
  ins "li a3, 10"
  line ".L_hex_loop:"
  ins "andi a4, a0, 15"
  ins "srli a0, a0, 4"
  ins "blt a4, a3, .L_hex_digit"
  ins "addi a4, a4, 39" -- 10–15 to 'a'–'f'
  line ".L_hex_digit:"
  ins "addi a4, a4, 48"
  ins "addi a2, a2, -1"
  ins "sb a4, 0(a2)"
  ins "bnez a0, .L_hex_loop"
  ins "addi a2, a2, -2"
  ins "li a4, 48"
  ins "sb a4, 0(a2)"
  ins "li a4, 120"
  ins "sb a4, 1(a2)"
  ins "mv a0, a2"
  ins "call _keel_print_str"
  ins "ld ra, 40(sp)"
  ins "addi sp, sp, 48"
  ins "ret"

  panic "_keel_panic_unhandled" "panic: unhandled operation\n"
  panic "_keel_panic_csr" "panic: csrRead or csrSet of a CSR other than mstatus, mie, mcause, mip\n"
  panic "_keel_panic_div" "panic: division by zero\n"
  panic "_keel_panic_bounds" "panic: array index out of bounds\n"
  panic "_keel_panic_overflow" "panic: arithmetic overflow\n"
  panic "_keel_panic_oom" "panic: out of memory\n"
  panic "_keel_panic_rc" "panic: reference count error\n"
  where
    fn lbl = line "\t.p2align 2" >> line (lbl ++ ":")
    -- RV32's 64-bit arithmetic and printing; a 64-bit value is (low, high) in a register pair.
    wideRuntime = do
      -- (a0, a1) · (a2, a3) → (a0, a1), and a2 = 1 when the product doesn't fit 64 bits
      -- (unsigned). Keeps t1, t3.
      fn "_keel_mulu64"
      mapM_ ins
        [ "mul a4, a0, a2", "mulhu a5, a0, a2", "mul a6, a0, a3", "mulhu a7, a0, a3"
        , "mul t4, a1, a2", "mulhu t5, a1, a2"
        , "snez t6, a1", "snez t0, a3", "and t6, t6, t0", "or t6, t6, a7", "or t6, t6, t5"
        , "add a5, a5, a6", "sltu t0, a5, a6", "or t6, t6, t0"
        , "add a5, a5, t4", "sltu t0, a5, t4", "or t6, t6, t0"
        , "mv a0, a4", "mv a1, a5", "snez a2, t6", "ret" ]
      -- The same, signed: multiply the magnitudes, then check and apply the sign. Keeps t1, t3.
      fn "_keel_muls64"
      mapM_ ins ["addi sp, sp, -16", "sw ra, 12(sp)", "xor t2, a1, a3", "sw t2, 0(sp)", "bgez a1, .L_muls_a"]
      negate "a0" "a1"
      line ".L_muls_a:"
      ins "bgez a3, .L_muls_b"
      negate "a2" "a3"
      line ".L_muls_b:"
      mapM_ ins ["call _keel_mulu64", "lw t2, 0(sp)", "bltz t2, .L_muls_neg", "srli t0, a1, 31", "or a2, a2, t0", "j .L_muls_ret"]
      line ".L_muls_neg:" -- the magnitude may be 2⁶³ at most
      li "t0" 0x80000000
      mapM_ ins ["bltu t0, a1, .L_muls_ovf", "bne a1, t0, .L_muls_negate", "beqz a0, .L_muls_negate"]
      line ".L_muls_ovf:"
      ins "li a2, 1"
      line ".L_muls_negate:"
      negate "a0" "a1"
      line ".L_muls_ret:"
      mapM_ ins ["lw ra, 12(sp)", "addi sp, sp, 16", "ret"]
      -- (a0, a1) / (a2, a3), unsigned → the quotient (a0, a1), the remainder (a2, a3); the
      -- divisor isn't 0. Shift and subtract, a bit at a time.
      fn "_keel_udivmod64"
      mapM_ ins ["li a4, 0", "li a5, 0", "li t6, 64"]
      line ".L_udiv_loop:"
      mapM_ ins
        [ "srli t1, a5, 31" -- the remainder's bit shifted out: it is then above the divisor
        , "slli a5, a5, 1", "srli t0, a4, 31", "or a5, a5, t0"
        , "slli a4, a4, 1", "srli t0, a1, 31", "or a4, a4, t0"
        , "slli a1, a1, 1", "srli t0, a0, 31", "or a1, a1, t0", "slli a0, a0, 1"
        , "bnez t1, .L_udiv_sub", "bltu a5, a3, .L_udiv_next", "bne a5, a3, .L_udiv_sub", "bltu a4, a2, .L_udiv_next" ]
      line ".L_udiv_sub:"
      mapM_ ins ["sltu t0, a4, a2", "sub a4, a4, a2", "sub a5, a5, a3", "sub a5, a5, t0", "ori a0, a0, 1"]
      line ".L_udiv_next:"
      mapM_ ins ["addi t6, t6, -1", "bnez t6, .L_udiv_loop", "mv a2, a4", "mv a3, a5", "ret"]
      -- Signed, truncating: the remainder takes the dividend's sign.
      fn "_keel_sdivmod64"
      mapM_ ins ["addi sp, sp, -16", "sw ra, 12(sp)", "sw a1, 0(sp)", "xor t0, a1, a3", "sw t0, 4(sp)", "bgez a1, .L_sdiv_a"]
      negate "a0" "a1"
      line ".L_sdiv_a:"
      ins "bgez a3, .L_sdiv_b"
      negate "a2" "a3"
      line ".L_sdiv_b:"
      mapM_ ins ["call _keel_udivmod64", "lw t0, 4(sp)", "bgez t0, .L_sdiv_q"]
      negate "a0" "a1"
      line ".L_sdiv_q:"
      mapM_ ins ["lw t0, 0(sp)", "bgez t0, .L_sdiv_r"]
      negate "a2" "a3"
      line ".L_sdiv_r:"
      mapM_ ins ["lw ra, 12(sp)", "addi sp, sp, 16", "ret"]
      -- (a0, a1) shifted by a2, from 0 to 63 (0 returns it: a shift by 32 - 0 would be by 0).
      fn "_keel_shl64"
      mapM_ ins ["beqz a2, .L_shl_ret", "li t0, 32", "bgeu a2, t0, .L_shl_big", "sub t0, t0, a2", "sll a1, a1, a2", "srl t4, a0, t0", "or a1, a1, t4", "sll a0, a0, a2", "ret"]
      line ".L_shl_big:"
      mapM_ ins ["addi a2, a2, -32", "sll a1, a0, a2", "li a0, 0"]
      line ".L_shl_ret:"
      ins "ret"
      forM_ [("_keel_shr64", "srl", "li a1, 0"), ("_keel_sra64", "sra", "srai a1, a1, 31")] $ \(l, op, fill) -> do
        fn l
        mapM_ ins ["beqz a2, " ++ l ++ "_ret", "li t0, 32", "bgeu a2, t0, " ++ l ++ "_big", "sub t0, t0, a2", "srl a0, a0, a2", "sll t4, a1, t0", "or a0, a0, t4", op ++ " a1, a1, a2", "ret"]
        line (l ++ "_big:")
        mapM_ ins ["addi a2, a2, -32", op ++ " a0, a1, a2", fill]
        line (l ++ "_ret:")
        ins "ret"
      -- Print (a0, a1) in decimal: digits backwards from 40(sp), the pointer at 44(sp).
      fn "_keel_print_u64w"
      mapM_ ins ["addi sp, sp, -64", "sw ra, 60(sp)", "addi t0, sp, 40", "sb zero, 0(t0)", "sw t0, 44(sp)"]
      line ".L_u64w_loop:"
      mapM_ ins
        [ "li a2, 10", "li a3, 0", "call _keel_udivmod64", "lw t0, 44(sp)", "addi t0, t0, -1"
        , "addi a2, a2, 48", "sb a2, 0(t0)", "sw t0, 44(sp)", "or t1, a0, a1", "bnez t1, .L_u64w_loop"
        , "mv a0, t0", "call _keel_print_str", "lw ra, 60(sp)", "addi sp, sp, 64", "ret" ]
      fn "_keel_print_i64w"
      ins "bgez a1, .L_i64w_pos"
      mapM_ ins ["addi sp, sp, -16", "sw ra, 12(sp)", "sw a0, 0(sp)", "sw a1, 4(sp)", "li a0, 45", "call _keel_putc", "lw a0, 0(sp)", "lw a1, 4(sp)", "lw ra, 12(sp)", "addi sp, sp, 16"]
      negate "a0" "a1"
      line ".L_i64w_pos:"
      ins "tail _keel_print_u64w"
    -- Negate the pair (lo, hi) (uses t0).
    negate lo hi = mapM_ ins ["snez t0, " ++ lo, "neg " ++ lo ++ ", " ++ lo, "neg " ++ hi ++ ", " ++ hi, "sub " ++ hi ++ ", " ++ hi ++ ", t0"]
    panic lbl msg = do
      l <- str msg
      fn lbl
      ins ("la a0, " ++ l)
      ins "call _keel_print_str"
      ins "li a0, 101"
      ins "tail _keel_exit"
