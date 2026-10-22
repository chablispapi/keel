-- | x86-64 back end: the lowered IR ("Keel.Lower") → x86-64 assembly for Linux (GNU as, Intel
-- syntax), linked with the C library by @gcc -no-pie@. The code generation follows
-- "Keel.AArch64": the common right-hand sides are computed straight into their variable's
-- register from their operands' registers, a comparison only an if uses becomes a branch, a
-- self tail call moves its arguments into the parameters at once, and a reduction over an
-- array runs in SSE registers. The rest is computed into rax and stored, as in "Keel.RiscV".
-- The hosted runtime (printf, files, KEEL_STATS) follows "Keel.AArch64".
--
-- Keel's own calling convention: rax = block / result, arguments in rdi, rsi, rdx, rcx, r8, r9,
-- r10. Variables live in rbx, r12–r15 (callee-saved, as for C) or in stack slots; rbp is the
-- frame pointer. Scratch: r11 and r10 hold operands, r9 and r8 temporaries (the allocator
-- leaves r8–r11 alone); rdx and rcx for division, shifts and inline reference counting. Calls
-- into the C library follow the System V ABI, with the stack 16-byte aligned at every call.
--
-- The heap is 16 GB of address space reserved with mmap (MAP_NORESERVE) at startup: pages
-- are only backed when touched.
module Keel.X86 (compileX86, linkCommand) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Data.Bits ((.|.), shiftL)
import Data.ByteString qualified as B
import Data.Char (isAscii, isPrint)
import Data.List (elemIndex, nub)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Keel.AArch64 (Loc (..), Reduction (..), allocate, bound, dataOf, header, maxSmall, prepare, printerTypes, reduction, template, uses)
import Keel.Lower
import Keel.Syntax
import Numeric (showOct)

compileX86 :: Program -> Either String String
compileX86 p = do
  (decls, t, lp) <- prepare p
  pure (emitProgram decls t lp)

-- | How to turn the assembly into a program on x86-64 Linux.
linkCommand :: FilePath -> FilePath -> (String, [String])
linkCommand s out = ("gcc", ["-no-pie", "-o", out, s])

heapReserve :: Integer
heapReserve = 16 * 1024 * 1024 * 1024

data GS = GS {gsLabel :: Int, gsLines :: [String], gsStrings :: M.Map String String, gsNullary :: S.Set Integer, gsLayouts :: M.Map (Integer, Int, Integer) Integer}

type G = State GS

line :: String -> G ()
line l = modify (\s -> s {gsLines = l : gsLines s})

ins :: String -> G ()
ins i = line ("\t" ++ i)

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
      let l = ".Lstr" ++ show (M.size m)
      modify (\st -> st {gsStrings = M.insert s l m})
      pure l

-- | A string for .asciz: printable ASCII as is, the rest as octal escapes of its UTF-8 bytes.
asciz :: String -> String
asciz s = "\"" ++ concatMap esc s ++ "\""
  where
    esc c
      | c == '"' || c == '\\' = ['\\', c]
      | isAscii c && isPrint c = [c]
      | otherwise = concat ["\\" ++ pad (showOct b "") | b <- B.unpack (TE.encodeUtf8 (T.singleton c))]
    pad o = replicate (3 - length o) '0' ++ o

printStr :: String -> G ()
printStr s = do
  l <- str s
  ins ("lea rax, [rip + " ++ l ++ "]")
  ins "call _keel_print_str"

-- | Load a constant (any 64-bit pattern, given as a mathematical integer).
li :: String -> Integer -> G ()
li r n
  | v >= -(2 ^ (31 :: Int)) && v < 2 ^ (31 :: Int) = ins ("mov " ++ r ++ ", " ++ show v)
  | otherwise = ins ("movabs " ++ r ++ ", " ++ show v)
  where
    u = n `mod` (2 ^ (64 :: Int))
    v = if u >= 2 ^ (63 :: Int) then u - 2 ^ (64 :: Int) else u

-- | A memory operand: qword (or dword) ptr [base + off].
mem, mem32 :: String -> Int -> String
mem b off = "qword ptr [" ++ b ++ disp off ++ "]"
mem32 b off = "dword ptr [" ++ b ++ disp off ++ "]"

disp :: Int -> String
disp off
  | off == 0 = ""
  | off > 0 = " + " ++ show off
  | otherwise = " - " ++ show (negate off)

-- | A 64-bit register's low 32 bits.
w32 :: String -> String
w32 r = case r of
  'r' : n@(d : _) | d `elem` ['0' .. '9'] -> 'r' : n ++ "d"
  'r' : rest -> 'e' : rest
  _ -> r

-- | Keel's argument registers: 0 is the block / result.
argReg :: Int -> String
argReg i = ["rax", "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10"] !! i

address :: String -> String -> G ()
address r sym = ins ("lea " ++ r ++ ", [rip + " ++ sym ++ "]")

emitProgram :: [Decl] -> Ty -> LProg -> String
emitProgram decls mainTy (LProg funs statics mainF _ layouts) = unlines (reverse (gsLines final))
  where
    final = execState gen (GS 0 [] M.empty S.empty layouts)
    printers = printerTypes decls mainTy
    gen = do
      line "\t.intel_syntax noprefix"
      line "\t.text"
      emitEntry printers mainTy
      forM_ (M.toList funs) $ \(i, f) -> emitFun ("_kf_" ++ show i) f
      emitFun "_kf_main" mainF
      forM_ (M.toList printers) $ \(_, (t, lbl)) -> emitPrinter decls printers lbl t
      emitRuntime
      line "\t.data"
      line "\t.p2align 3"
      forM_ statics $ \(i, name, fs) -> do
        ins ".quad 0x80000000\t\t# header: immortal"
        line ("_kc_" ++ show i ++ ":\t\t\t# static block of " ++ name)
        forM_ fs $ \f -> ins (".quad _kf_" ++ show f)
      tags <- gets gsNullary
      forM_ (S.toList tags) $ \t -> do
        ins (".quad " ++ show (header layouts t .|. 0x80000000) ++ "\t\t# header: immortal, layout " ++ show t)
        line ("_kn_" ++ show t ++ ":\t\t\t# every constructor without fields with this layout")
      -- The words and pointer map of each layout whose header holds a field (spec/memory.md).
      line "\t.p2align 2"
      line "_keel_layouts:"
      let byId = M.fromList [(i, (n, bm)) | ((_, n, bm), i) <- M.toList layouts]
      forM_ [fieldLayouts .. maybe (fieldLayouts - 1) fst (M.lookupMax byId)] $ \i ->
        ins (".long " ++ show (maybe 0 (\(n, bm) -> toInteger n .|. (bm `shiftL` 8)) (M.lookup i byId)))
      line "\t.p2align 3"
      line "_keel_heap_ptr:" -- set by main: the heap's next free byte, and its end
      ins ".quad 0, 0"
      line "_keel_arena_base:" -- as in "Keel.AArch64"
      ins ".quad -1"
      line "_keel_arena_top:"
      ins ".quad 0"
      line "_keel_fl:"
      ins ".quad _keel_freelists"
      line "\t.bss"
      line "\t.p2align 3"
      line "_keel_freelists:"
      ins (".zero " ++ show (8 * (maxSmall + 1)))
      line "_keel_nofree:"
      ins (".zero " ++ show (8 * (maxSmall + 1)))
      line "_keel_stats:"
      ins ".zero 32"
      line "_keel_handlers:"
      ins ".zero 8"
      line "\t.section .rodata"
      strs <- gets gsStrings
      forM_ (M.toList strs) $ \(s, l) -> line (l ++ ":\t.asciz " ++ asciz s)
      line "\t.section .note.GNU-stack,\"\",@progbits"

-- Functions -------------------------------------------------------------------------------

-- | A function's frame: where each variable lives and which registers to restore (allocation
-- as in "Keel.AArch64", with rbx and r12–r15). fLoop: the function's own label, when a call to
-- itself in tail position can move its arguments into the parameters and jump back. fUses: how
-- often each variable occurs (a comparison used once, by an if, becomes a branch).
data Slots = Slots {fLocs :: M.Map String Loc, fSaved :: [(String, Int)], fLoop :: Maybe String, fUses :: M.Map String Int, fParams :: [String]}

emitFun :: String -> Fun -> G ()
emitFun lbl f@(Fun name params base env envPtrs dropsSelf body) = do
  when (length params > 7) $ error "more than 7 parameters"
  let (locs, saved, frame) = allocate ["rbx", "r12", "r13", "r14", "r15"] f (params ++ env ++ bound body)
      slots = Slots locs saved (if null env && not dropsSelf then Just lbl else Nothing) (M.fromListWith (+) [(v, 1) | v <- uses body]) params
  line "\t.p2align 4"
  line (lbl ++ ":\t\t\t# " ++ name)
  ins "push rbp"
  ins "mov rbp, rsp"
  when (frame > 0) $ ins ("sub rsp, " ++ show frame)
  forM_ saved $ \(r, off) -> ins ("mov " ++ mem "rsp" off ++ ", " ++ r)
  forM_ (zip [base ..] env) $ \(j, v) -> do
    ins ("mov r11, " ++ mem "rax" (8 * j))
    store slots "r11" v
  forM_ (zip [1 ..] params) $ \(r, p) -> store slots (argReg r) p
  forM_ (fLoop slots >> reduction lbl f) (vectorLoop slots)
  line (".L" ++ lbl ++ "_loop:")
  forM_ envPtrs $ \v -> dup slots v
  when dropsSelf $ ins "call _keel_drop" -- rax is still the block
  expr slots Nothing body

-- | Leave a Keel function: restore its callee-saved registers, then the frame.
leave :: Slots -> G ()
leave slots = do
  forM_ (fSaved slots) $ \(r, off) -> ins ("mov " ++ r ++ ", " ++ mem "rsp" off)
  ins "mov rsp, rbp"
  ins "pop rbp"

store, load' :: Slots -> String -> String -> G ()
store slots r v = case fLocs slots M.! v of
  InReg x -> unless (x == r) $ ins ("mov " ++ x ++ ", " ++ r)
  InSlot i -> ins ("mov " ++ mem "rsp" (8 * i) ++ ", " ++ r)
load' slots r v = case fLocs slots M.! v of
  InReg x -> unless (x == r) $ ins ("mov " ++ r ++ ", " ++ x)
  InSlot i -> ins ("mov " ++ r ++ ", " ++ mem "rsp" (8 * i))

atom :: Slots -> String -> Atom -> G ()
atom slots r a = case a of
  AInt n -> li r n
  AVar v -> load' slots r v
  AGlobal i -> address r ("_kc_" ++ show i)
  ANullary t -> modify (\s -> s {gsNullary = S.insert t (gsNullary s)}) >> address r ("_kn_" ++ show t)

-- | Increment a reference count inline (r11, edx). The header's low half (spec/memory.md): the
-- count moves by 1024, an immortal block is negative, and a count of 0 is a freed block.
dup :: Slots -> String -> G ()
dup slots v = do
  lSkip <- newLabel
  load' slots "r11" v
  ins ("mov edx, " ++ mem32 "r11" (-8))
  ins "test edx, edx"
  ins ("js " ++ lSkip)
  ins "sub edx, 1024"
  ins "js _keel_panic_rc"
  ins "add edx, 2048"
  ins ("mov " ++ mem32 "r11" (-8) ++ ", edx")
  line (lSkip ++ ":")

expr :: Slots -> Maybe (String, String) -> Expr -> G ()
expr slots join e = case e of
  Ret a -> do
    atom slots "rax" a
    case join of
      Nothing -> leave slots >> ins "ret"
      Just (v, lbl) -> store slots "rax" v >> ins ("jmp " ++ lbl)
  Bind x rhs (Ret (AVar y)) | x == y, Nothing <- join, Just tc <- tailCall rhs -> tc
  -- A comparison used only by the if after it: compare and branch, no 0/1 value.
  Bind c (RPrim op it a b) (BindIf x (AVar c') ea eb rest)
    | c == c', op `elem` [Eq, Lt], M.lookup c (fUses slots) == Just 2 -> do
        ra <- operand slots "r11" a
        rb <- operandI slots "r10" b
        ins ("cmp " ++ ra ++ ", " ++ rb)
        let jElse = if op == Eq then "jne" else if signed it then "jge" else "jae"
        ifThen x (\l -> ins (jElse ++ " " ++ l)) ea eb rest
  Bind x rhs rest -> do
    let d = destOf slots x
    direct <- rhsInto slots d rhs
    unless direct (rhsCode slots rhs)
    when (not direct || d == "rax") $ store slots "rax" x
    expr slots join rest
  BindIf x c a b rest -> do
    rc <- operand slots "r11" c
    ins ("test " ++ rc ++ ", " ++ rc)
    ifThen x (\l -> ins ("jz " ++ l)) a b rest
  BindCase x s bs rest -> do
    let tailPos = isNothingJ && returns x rest
    lJoin <- newLabel
    labels <- mapM (const newLabel) bs
    atom slots "r11" s
    ins ("mov r11d, " ++ mem32 "r11" (-8))
    ins "and r11d, 0x3ff" -- the layout, in the header
    -- Compare against every layout but the last, whose branch comes first and falls through.
    forM_ (zip (init bs) labels) $ \((tag, _, _), l) -> do
      ins ("cmp r11d, " ++ show tag)
      ins ("je " ++ l)
    forM_ (zip (last bs : init bs) (last labels : init labels)) $ \((_, _, body), l) -> do
      line (l ++ ":")
      expr slots (target tailPos x lJoin) body
    unless tailPos $ do
      line (lJoin ++ ":")
      expr slots join rest
  Dup v rest -> dup slots v >> expr slots join rest
  Drop v rest -> do
    load' slots "rax" v
    ins "call _keel_drop"
    expr slots join rest
  DropReuse v tok rest -> do
    load' slots "rax" v
    ins "call _keel_drop_reuse"
    store slots "rax" tok
    expr slots join rest
  where
    isNothingJ = case join of
      Nothing -> True
      Just _ -> False
    returns x (Ret (AVar y)) = x == y
    returns _ _ = False
    target tailPos x lJoin = if tailPos then Nothing else Just (x, lJoin)

    -- let x = (if … then a else b) in rest, with @jumpElse l@ branching to the else part.
    ifThen :: String -> (String -> G ()) -> Expr -> Expr -> Expr -> G ()
    ifThen x jumpElse a b rest = do
      let tailPos = isNothingJ && returns x rest
      lElse <- newLabel
      lJoin <- newLabel
      jumpElse lElse
      expr slots (target tailPos x lJoin) a
      line (lElse ++ ":")
      expr slots (target tailPos x lJoin) b
      unless tailPos $ do
        line (lJoin ++ ":")
        expr slots join rest

    tailCall rhs = case rhs of
      RCall f a -> Just $ do
        atom slots "rax" f
        atom slots "rdi" a
        ins ("mov r11, " ++ mem "rax" 0)
        leave slots
        ins "jmp r11"
      RCallKnown i as
        | fLoop slots == Just ("_kf_" ++ show i) -> Just $ do
            moves slots [(fLocs slots M.! p, a) | (p, a) <- zip (fParams slots) as]
            ins ("jmp .L_kf_" ++ show i ++ "_loop")
        | otherwise -> Just $ do
            forM_ (zip [1 ..] as) $ \(r, a) -> atom slots (argReg r) a
            leave slots
            ins ("jmp _kf_" ++ show i)
      RProj a i -> Just $ do
        atom slots "rax" a
        ins "xor edi, edi"
        ins ("mov r11, " ++ mem "rax" (8 * i))
        leave slots
        ins "jmp r11"
      _ -> Nothing

-- | The register holding an atom: its own, if it lives in one; otherwise it is loaded into r.
operand :: Slots -> String -> Atom -> G String
operand slots r a = case a of
  AVar v | InReg x <- fLocs slots M.! v -> pure x
  _ -> atom slots r a >> pure r

-- | An instruction's second operand: a 32-bit immediate, or a register.
operandI :: Slots -> String -> Atom -> G String
operandI slots r a = case a of
  AInt n | n >= -(2 ^ (31 :: Int)), n < 2 ^ (31 :: Int) -> pure (show n)
  _ -> operand slots r a

-- | Where a variable is computed: its own register, or rax when it lives in a slot.
destOf :: Slots -> String -> String
destOf slots x = case fLocs slots M.! x of
  InReg r -> r
  InSlot _ -> "rax"

-- | The common right-hand sides, computed straight into register d from their operands'
-- registers; False for the rest (rhsCode computes those into rax). d is written only after
-- the operands are read, or through r11, since it may share a register with an operand that
-- dies here.
rhsInto :: Slots -> String -> Rhs -> G Bool
rhsInto slots d rhs = case rhs of
  RAtom a -> atom slots d a >> pure True
  RPrim Eq _ a b -> compare' a b "sete"
  RPrim Lt it a b -> compare' a b (if signed it then "setl" else "setb")
  RPrim (Arith ov aop) (IntTy sgn 64) a b
    | ov `elem` [Wrap, Checked], aop `elem` [Add, Sub] || (aop == Mul && (sgn || ov == Wrap)) -> do
        binop (case aop of Add -> "add"; Sub -> "sub"; _ -> "imul") (aop /= Sub) (aop /= Mul) a b
        when (ov == Checked) $ ins ((if sgn then "jo" else "jc") ++ " _keel_panic_overflow")
        pure True
  -- Canonical (sign- or zero-extended) operands give a canonical result: any width.
  RPrim (Bits bop) _ a b | bop `elem` [And, Or, Xor] -> do
    binop (case bop of And -> "and"; Or -> "or"; _ -> "xor") True True a b
    pure True
  -- A shift by a constant in range: one instruction. A right shift of a canonical value stays
  -- canonical; a left shift only at 64 bits, where nothing needs re-extending.
  RPrim (Bits bop) (IntTy sgn n) a (AInt k)
    | k >= 0, k < 64, bop == Shr || (bop == Shl && n == 64) -> do
        ra <- operand slots "r11" a
        unless (ra == d) $ ins ("mov " ++ d ++ ", " ++ ra)
        ins ((if bop == Shl then "shl " else if sgn then "sar " else "shr ") ++ d ++ ", " ++ show k)
        pure True
  -- Division by a constant that is neither 0 nor -1 can't panic.
  RPrim (Arith Checked aop) (IntTy sgn _) a (AInt k)
    | aop `elem` [Div, Rem], k /= 0, k /= -1 || not sgn -> do
        atom slots "rax" a
        li "r10" k
        if sgn then ins "cqo" >> ins "idiv r10" else ins "xor edx, edx" >> ins "div r10"
        let r = if aop == Div then "rax" else "rdx"
        unless (r == d) $ ins ("mov " ++ d ++ ", " ++ r)
        pure True
  RField a i -> do
    ra <- operand slots "r11" a
    ins ("mov " ++ d ++ ", " ++ mem ra (8 * i))
    pure True
  RHeader a sgn -> do
    ra <- operand slots "r11" a
    ins (narrowLoad sgn d ++ mem32 ra (-4))
    pure True
  -- To a 64-bit type the canonical form doesn't change: a move.
  RConv to a | bits to == 64 -> atom slots d a >> pure True
  RArray ALength _ [a] -> do
    ra <- operand slots "r11" a
    ins ("mov " ++ d ++ ", " ++ mem ra 0)
    pure True
  RArray AGet e [a, i] -> do
    ra <- operand slots "r11" a
    ri <- operand slots "r10" i
    ins ("cmp " ++ ri ++ ", " ++ mem ra 0)
    ins "jae _keel_panic_bounds" -- unsigned: a negative index is out of bounds too
    elementInto e d ra ri
    pure True
  RIndex a i e -> do
    ra <- operand slots "r11" a
    ri <- operand slots "r10" i
    elementInto e d ra ri
    pure True
  _ -> pure False
  where
    compare' a b set = do
      ra <- operand slots "r11" a
      rb <- operandI slots "r10" b
      ins ("cmp " ++ ra ++ ", " ++ rb)
      ins (set ++ " al")
      ins ("movzx " ++ w32 d ++ ", al")
      pure True
    -- d = a op b, in x86's two-operand form; b may be an immediate (not for imul's).
    binop op commutative immOk a b = do
      ra <- operand slots "r11" a
      rb <- (if immOk then operandI else operand) slots "r10" b
      case () of
        _
          | ra == d -> ins (op ++ " " ++ d ++ ", " ++ rb)
          | rb == d && commutative -> ins (op ++ " " ++ d ++ ", " ++ ra)
          | rb == d -> do
              unless (ra == "r11") $ ins ("mov r11, " ++ ra)
              ins (op ++ " r11, " ++ rb)
              ins ("mov " ++ d ++ ", r11")
          | otherwise -> ins ("mov " ++ d ++ ", " ++ ra) >> ins (op ++ " " ++ d ++ ", " ++ rb)

-- | Load element ri of array ra into d.
elementInto :: Elem -> String -> String -> String -> G ()
elementInto e d ra ri = case e of
  ENarrow sgn -> ins (narrowLoad sgn d ++ "dword ptr [" ++ ra ++ " + " ++ ri ++ "*4 + 16]")
  _ -> ins ("mov " ++ d ++ ", qword ptr [" ++ ra ++ " + " ++ ri ++ "*8 + 16]")

-- | Move atoms into locations all at once (a self tail call's arguments into its parameters):
-- a move waits while its destination is still to be read; a cycle goes through a scratch
-- register (at most three cycles among seven parameters). r11 carries slot-to-slot moves.
moves :: Slots -> [(Loc, Atom)] -> G ()
moves slots ms0 = go [(d, src a) | (d, a) <- ms0, src a /= Left d] ["r8", "r9", "r10", "rdx", "rcx", "rsi"]
  where
    src a = case a of
      AVar v -> Left (fLocs slots M.! v)
      _ -> Right a
    go [] _ = pure ()
    go ms scratch = case [m | m@(d, _) <- ms, Left d `notElem` map snd ms] of
      m : _ -> move m >> go (filter (/= m) ms) scratch
      [] -> case (ms, scratch) of
        ((d, _) : _, r : rs) -> do
          move (InReg r, Left d)
          go [(d', if s' == Left d then Left (InReg r) else s') | (d', s') <- ms] rs
        _ -> error "moves: out of scratch registers"
    move (d, s) = case (d, s) of
      (InReg r, Left l) -> load r l
      (InReg r, Right a) -> atom slots r a
      (InSlot i, Left (InReg r)) -> ins ("mov " ++ mem "rsp" (8 * i) ++ ", " ++ r)
      (InSlot i, Left l) -> load "r11" l >> ins ("mov " ++ mem "rsp" (8 * i) ++ ", r11")
      (InSlot i, Right a) -> atom slots "r11" a >> ins ("mov " ++ mem "rsp" (8 * i) ++ ", r11")
    load r l = case l of
      InReg x -> unless (x == r) $ ins ("mov " ++ r ++ ", " ++ x)
      InSlot i -> ins ("mov " ++ r ++ ", " ++ mem "rsp" (8 * i))

-- | A reduction over an array ("Keel.AArch64".reduction) four elements at a time in SSE
-- registers, two 64-bit lanes each: from the current i to the last multiple of four before
-- the end, then the scalar loop does the rest. 4-byte elements are widened as they are loaded
-- (pmovsxdq / pmovzxdq, SSE4.1). With a checked acc + e the result is kept only if every e was
-- ≥ 0 and no lane's sum overflowed, as on ARM: then the checked adds of the lanes panic
-- exactly when the scalar loop would; otherwise the scalar loop redoes those elements (the
-- loop is pure).
--
-- Registers: xmm0, xmm1 the lane sums, xmm2, xmm3 the sign bits seen (two chains), xmm4 the
-- ORs feeding them, xmm5–xmm7 the invariants and constants, xmm8, xmm9 the elements,
-- xmm10–xmm15 the other values (two each).
vectorLoop :: Slots -> Reduction -> G ()
vectorLoop slots red = when (length scalars <= 3 && length (rNodes red) <= 3) $ do
  lSkip <- newLabel
  lLoop <- newLabel
  atom slots "r11" (AVar (rXs red))
  atom slots "r10" (AVar (rI red))
  ins "mov rcx, qword ptr [r11]"
  ins "sub rcx, r10"
  ins "cmp rcx, 4"
  ins ("jl " ++ lSkip)
  ins "and rcx, -4"
  ins ("lea r8, [r11 + r10*" ++ show size ++ " + 16]")
  ins ("lea r9, [r8 + rcx*" ++ show size ++ "]")
  forM_ ["xmm0", "xmm1", "xmm2", "xmm3"] $ \x -> ins ("pxor " ++ x ++ ", " ++ x)
  forM_ (zip scalars [5 :: Int ..]) $ \(a, k) -> do
    atom slots "rdx" a
    ins ("movq xmm" ++ show k ++ ", rdx")
    ins ("punpcklqdq xmm" ++ show k ++ ", xmm" ++ show k)
  line (lLoop ++ ":")
  case rElem red of
    ENarrow sgn -> do
      let x = if sgn then "pmovsxdq" else "pmovzxdq"
      ins (x ++ " xmm8, qword ptr [r8]")
      ins (x ++ " xmm9, qword ptr [r8 + 8]")
    _ -> ins "movdqu xmm8, xmmword ptr [r8]" >> ins "movdqu xmm9, xmmword ptr [r8 + 16]"
  ins ("add r8, " ++ show (4 * size))
  forM_ (rNodes red) $ \(t, op, a, b) -> forM_ [0, 1] $ \h -> do
    ins ("movdqa " ++ vreg (AVar t) h ++ ", " ++ vreg a h)
    ins (opName op ++ " " ++ vreg (AVar t) h ++ ", " ++ vreg b h)
  let e = AVar (rE red)
  forM_ [0, 1] $ \h -> ins ("paddq xmm" ++ show h ++ ", " ++ vreg e h)
  when (rChecked red) $ do
    ins ("movdqa xmm4, " ++ vreg e 0)
    ins ("por xmm4, " ++ vreg e 1)
    ins "por xmm2, xmm4"
    ins "movdqa xmm4, xmm0"
    ins "por xmm4, xmm1"
    ins "por xmm3, xmm4"
  ins "cmp r8, r9"
  ins ("jne " ++ lLoop)
  when (rChecked red) $ do
    ins "por xmm2, xmm3"
    ins "movmskpd edx, xmm2" -- the lanes' sign bits
    ins "test edx, edx"
    ins ("jnz " ++ lSkip)
  atom slots "rsi" (AVar (rAcc red))
  forM_ [(x, lane) | x <- ["xmm0", "xmm1"], lane <- [0, 1 :: Int]] $ \(x, lane) -> do
    ins (if lane == 0 then "movq rdx, " ++ x else "pextrq rdx, " ++ x ++ ", 1")
    ins "add rsi, rdx"
    when (rChecked red) $ ins "jo _keel_panic_overflow"
  ins "add r10, rcx"
  store slots "r10" (rI red)
  store slots "rsi" (rAcc red)
  line (lSkip ++ ":")
  where
    size = case rElem red of
      ENarrow _ -> 4 :: Int
      _ -> 8
    temps = rElems red ++ [t | (t, _, _, _) <- rNodes red]
    scalars = nub [o | (_, _, a, b) <- rNodes red, o <- [a, b], case o of AVar v -> v `notElem` temps; _ -> True]
    vreg a h = case a of
      AVar v | v `elem` rElems red -> "xmm" ++ show (8 + h :: Int)
      AVar v | Just k <- elemIndex v [t | (t, _, _, _) <- rNodes red] -> "xmm" ++ show (10 + 2 * k + h)
      _ -> "xmm" ++ show (5 + fromMaybe 0 (elemIndex a scalars))
    opName op = case op of
      Bits And -> "pand"
      Bits Or -> "por"
      Bits Xor -> "pxor"
      Arith _ Sub -> "psubq"
      _ -> "paddq"

-- | Allocate a block into rax (header written). Clobbers rax, rcx, rdx, rsi, rdi only.
alloc :: Int -> Integer -> G ()
alloc n lid = do
  t <- gets (\st -> template (gsLayouts st) lid)
  li "rax" (toInteger n)
  li "rdi" t
  ins "call _keel_alloc"

rhsCode :: Slots -> Rhs -> G ()
rhsCode slots rhs = case rhs of
  RAtom a -> atom slots "rax" a
  RPrim op it a b -> do
    atom slots "r11" a
    atom slots "r10" b
    case op of
      Eq -> ins "cmp r11, r10" >> ins "sete al" >> ins "movzx eax, al"
      Lt -> ins "cmp r11, r10" >> ins ((if signed it then "setl" else "setb") ++ " al") >> ins "movzx eax, al"
      Arith _ aop | aop `elem` [Div, Rem] -> divide it aop
      Arith ov aop -> arith it ov aop
      Bits bop -> bitwise it bop
  RCall f a -> do
    atom slots "rax" f
    atom slots "rdi" a
    ins ("call " ++ mem "rax" 0)
  RCallKnown i as -> do
    forM_ (zip [1 ..] as) $ \(r, a) -> atom slots (argReg r) a
    ins ("call _kf_" ++ show i)
  RClosure i fvs lid -> do
    alloc (1 + length fvs) lid
    address "r9" ("_kf_" ++ show i)
    ins ("mov " ++ mem "rax" 0 ++ ", r9")
    storeAll 1 fvs
  RCodata is fvs lid -> do
    alloc (length is + length fvs) lid
    forM_ (zip [0 ..] is) $ \(j, i) -> do
      address "r9" ("_kf_" ++ show i)
      ins ("mov " ++ mem "rax" (8 * j) ++ ", r9")
    storeAll (length is) fvs
  RProj a i -> do
    atom slots "rax" a
    ins "xor edi, edi"
    ins ("call " ++ mem "rax" (8 * i))
  RAlloc lid h as -> do
    alloc (length as) lid
    fields h as
  RAllocAt tok lid h as -> do
    lFresh <- newLabel
    lDone <- newLabel
    load' slots "rax" tok
    ins "test rax, rax"
    ins ("jz " ++ lFresh)
    gets (\st -> header (gsLayouts st) lid) >>= li "r9"
    ins ("mov " ++ mem "rax" (-8) ++ ", r9")
    ins "inc qword ptr [rip + _keel_stats + 16]"
    ins ("jmp " ++ lDone)
    line (lFresh ++ ":")
    alloc (length as) lid
    line (lDone ++ ":")
    fields h as
  RField a i -> atom slots "r11" a >> ins ("mov rax, " ++ mem "r11" (8 * i))
  RHeader a sgn -> atom slots "r11" a >> ins (narrowLoad sgn "rax" ++ mem32 "r11" (-4))
  RPushHandler cs lid -> do
    alloc (2 + 2 * length cs) lid
    ins "mov r9, qword ptr [rip + _keel_handlers]"
    ins ("mov " ++ mem "rax" 0 ++ ", r9") -- the enclosing frame
    li "r9" (toInteger (length cs))
    ins ("mov " ++ mem "rax" 8 ++ ", r9")
    forM_ (zip [0 ..] cs) $ \(i, (n, a)) -> do
      li "r9" (toInteger n)
      ins ("mov " ++ mem "rax" (8 * (2 + 2 * i)) ++ ", r9")
      atom slots "r9" a
      ins ("mov " ++ mem "rax" (8 * (3 + 2 * i)) ++ ", r9")
    ins "mov qword ptr [rip + _keel_handlers], rax"
  RPopHandler a -> do
    atom slots "rax" a
    ins ("mov r11, " ++ mem "rax" 0)
    ins "mov qword ptr [rip + _keel_handlers], r11"
    ins "call _keel_drop"
    ins "xor eax, eax"
  RPerform n a -> do
    atom slots "rdi" a
    li "rax" (toInteger n)
    ins "call _keel_perform"
  RConv to a -> atom slots "rax" a >> canonical to
  RArena True -> ins "call _keel_arena_open"
  RArena False -> ins "call _keel_arena_close"
  RArray ALength _ [a] -> atom slots "r11" a >> ins ("mov rax, " ++ mem "r11" 0)
  RArray AGet e [a, i] -> do
    atom slots "r11" a
    atom slots "r10" i
    ins ("cmp r10, " ++ mem "r11" 0)
    ins "jae _keel_panic_bounds" -- unsigned: a negative index is out of bounds too
    element e
  RIndex a i e -> atom slots "r11" a >> atom slots "r10" i >> element e
  RArray op e as -> do
    forM_ (zip [0 ..] as) $ \(r, a) -> atom slots (argReg r) a
    case op of
      AEmpty -> ins "xor eax, eax" >> li "rdi" (elemKind e) >> ins "call _keel_array_alloc"
      ANew -> li "rsi" (elemKind e) >> ins "call _keel_array_new"
      ASet -> ins "call _keel_array_set"
      -- A unique array with room: store and count, without calling the runtime.
      APush -> do
        lSlow <- newLabel
        lDone <- newLabel
        ins "mov rcx, qword ptr [rax]"
        ins "cmp rcx, qword ptr [rax + 8]"
        ins ("jae " ++ lSlow)
        ins "mov edx, dword ptr [rax - 8]"
        ins "shr edx, 10"
        ins "cmp edx, 1"
        ins ("jne " ++ lSlow)
        ins $ case e of
          ENarrow _ -> "mov dword ptr [rax + rcx*4 + 16], edi"
          _ -> "mov qword ptr [rax + rcx*8 + 16], rdi"
        ins "inc rcx"
        ins "mov qword ptr [rax], rcx"
        ins ("jmp " ++ lDone)
        line (lSlow ++ ":")
        ins "call _keel_array_push"
        line (lDone ++ ":")
      _ -> ins "call _keel_array_pop"
  where
    storeAll :: Int -> [String] -> G ()
    storeAll from vs = forM_ (zip [from ..] vs) $ \(j, v) -> do
      load' slots "r9" v
      ins ("mov " ++ mem "rax" (8 * j) ++ ", r9")
    fields :: Maybe Atom -> [Atom] -> G ()
    fields h as = do
      forM_ h $ \a -> atom slots "r9" a >> ins ("mov " ++ mem32 "rax" (-4) ++ ", r9d")
      forM_ (zip [0 ..] as) $ \(j, a) -> do
        atom slots "r9" a
        ins ("mov " ++ mem "rax" (8 * j) ++ ", r9")

-- | The instruction that loads a 32-bit field into a 64-bit register, sign- or zero-extended:
-- followed by its memory operand.
narrowLoad :: Bool -> String -> String
narrowLoad sgn r = if sgn then "movsxd " ++ r ++ ", " else "mov " ++ w32 r ++ ", "

-- | Load element r10 of array r11 into rax.
element :: Elem -> G ()
element e = case e of
  ENarrow sgn -> ins (narrowLoad sgn "rax" ++ "dword ptr [r11 + r10*4 + 16]")
  _ -> ins "mov rax, qword ptr [r11 + r10*8 + 16]"

-- | Checked division (r11 / r10 into rax), as in "Keel.AArch64". x86 traps on min / -1 even for
-- the remainder, so a divisor of -1 is handled without dividing.
divide :: IntTy -> ArithOp -> G ()
divide it@(IntTy sgn n) aop = do
  lDone <- newLabel
  ins "test r10, r10"
  ins "jz _keel_panic_div"
  when sgn $ do
    lDivide <- newLabel
    ins "cmp r10, -1"
    ins ("jne " ++ lDivide)
    case aop of
      Div -> do
        li "r9" (fst (intRange it))
        ins "cmp r11, r9"
        ins "je _keel_panic_overflow"
        ins "mov rax, r11"
        ins "neg rax"
      _ -> ins "xor eax, eax"
    ins ("jmp " ++ lDone)
    line (lDivide ++ ":")
  ins "mov rax, r11"
  if sgn then ins "cqo" >> ins "idiv r10" else ins "xor edx, edx" >> ins "div r10"
  when (aop /= Div) $ ins "mov rax, rdx"
  line (lDone ++ ":")
  when (sgn && n < 64 && aop == Div) $ do
    li "r9" (snd (intRange it))
    ins "cmp rax, r9"
    ins "jg _keel_panic_overflow"

-- | Re-extend rax to the canonical form of an integer type.
canonical :: IntTy -> G ()
canonical (IntTy sgn n)
  | n == 64 = pure ()
  | sgn = ins (case n of 8 -> "movsx rax, al"; 16 -> "movsx rax, ax"; _ -> "movsxd rax, eax")
  | otherwise = ins (case n of 8 -> "movzx eax, al"; 16 -> "movzx eax, ax"; _ -> "mov eax, eax")

-- | Arithmetic with r11, r10 as operands and the result in rax (spec §2.5).
arith :: IntTy -> Overflow -> ArithOp -> G ()
arith it@(IntTy sgn n) ov aop
  | ov == Wrap = plain >> when narrow (canonical it)
  | otherwise = do
      lOvf <- if ov == Checked then pure "_keel_panic_overflow" else newLabel
      detect lOvf
      case ov of
        Saturate -> do
          lDone <- newLabel
          ins ("jmp " ++ lDone)
          line (lOvf ++ ":")
          saturate
          line (lDone ++ ":")
        Optional -> do
          lDone <- newLabel
          (none, some) <- gets (\st -> optionLayouts (gsLayouts st) it)
          ins "mov r8, rax" -- the allocator leaves r8–r11 alone
          if n <= 32
            then alloc 0 some >> ins ("mov " ++ mem32 "rax" (-4) ++ ", r8d")
            else alloc 1 some >> ins ("mov " ++ mem "rax" 0 ++ ", r8")
          ins ("jmp " ++ lDone)
          line (lOvf ++ ":")
          atom (Slots M.empty [] Nothing M.empty []) "rax" (ANullary none)
          line (lDone ++ ":")
        _ -> pure ()
  where
    narrow = n < 64
    (lo, hi) = intRange it
    plain = do
      ins "mov rax, r11"
      ins ((case aop of Add -> "add"; Sub -> "sub"; _ -> "imul") ++ " rax, r10")
    detect lOvf
      | narrow && sgn = do
          plain -- exact: narrow operands can't overflow 64 bits
          li "r9" lo
          ins "cmp rax, r9"
          ins ("jl " ++ lOvf)
          li "r9" hi
          ins "cmp rax, r9"
          ins ("jg " ++ lOvf)
      | narrow = do
          plain
          li "r9" hi
          ins "cmp rax, r9"
          ins ("ja " ++ lOvf)
      | sgn = plain >> ins ("jo " ++ lOvf)
      | aop == Mul = ins "mov rax, r11" >> ins "mul r10" >> ins ("jc " ++ lOvf)
      | otherwise = plain >> ins ("jc " ++ lOvf)
    saturate
      | narrow && sgn = do
          lLow <- newLabel
          lEnd <- newLabel
          li "r9" lo
          ins "cmp rax, r9"
          ins ("jl " ++ lLow)
          li "rax" hi
          ins ("jmp " ++ lEnd)
          line (lLow ++ ":")
          ins "mov rax, r9"
          line (lEnd ++ ":")
      | not sgn = if aop == Sub then ins "xor eax, eax" else li "rax" hi
      | otherwise = do
          -- The direction: the sign of the first operand (of the product, for a product).
          lEnd <- newLabel
          ins "mov rcx, r11"
          when (aop == Mul) $ ins "xor rcx, r10"
          li "rax" hi
          ins "test rcx, rcx"
          ins ("jns " ++ lEnd)
          li "rax" lo
          line (lEnd ++ ":")

-- | Bitwise operations with r11, r10 as operands and the result in rax, matching the
-- evaluator: a shift by a negative amount is a shift by 0, and by 64 or more shifts everything
-- out.
bitwise :: IntTy -> BitOp -> G ()
bitwise it@(IntTy sgn n) bop = case bop of
  And -> ins "mov rax, r11" >> ins "and rax, r10"
  Or -> ins "mov rax, r11" >> ins "or rax, r10"
  Xor -> ins "mov rax, r11" >> ins "xor rax, r10"
  Shl -> shift "shl" >> when (n < 64) (canonical it)
  Shr -> shift (if sgn then "sar" else "shr")
  where
    shift instr = do
      lPos <- newLabel
      lBig <- newLabel
      lDone <- newLabel
      ins "mov rcx, r10"
      when sgn $ do
        ins "test rcx, rcx"
        ins ("jns " ++ lPos)
        ins "xor ecx, ecx"
      line (lPos ++ ":")
      ins "cmp rcx, 63"
      ins ("ja " ++ lBig)
      ins "mov rax, r11"
      ins (instr ++ " rax, cl")
      ins ("jmp " ++ lDone)
      line (lBig ++ ":")
      if instr == "sar" then ins "mov rax, r11" >> ins "sar rax, 63" else ins "xor eax, eax"
      line (lDone ++ ":")

-- Results ---------------------------------------------------------------------------------

-- | A printer: value in rax (borrowed), prints it in the reference evaluator's format.
emitPrinter :: [Decl] -> M.Map String (Ty, String) -> String -> Ty -> G ()
emitPrinter decls printers lbl t = do
  line "\t.p2align 4"
  line (lbl ++ ":\t\t\t# print " ++ prettyTy t)
  ins "push rbp"
  ins "mov rbp, rsp"
  ins "sub rsp, 16"
  ins ("mov " ++ mem "rsp" 0 ++ ", rax") -- the value; [rsp + 8] an array's index
  case t of
    TInt (IntTy sgn _) -> ins (if sgn then "call _keel_print_i64" else "call _keel_print_u64")
    TBool -> do
      lFalse <- newLabel
      lDone <- newLabel
      ins "test rax, rax"
      ins ("jz " ++ lFalse)
      printStr "true"
      ins ("jmp " ++ lDone)
      line (lFalse ++ ":")
      printStr "false"
      line (lDone ++ ":")
    TUnit -> printStr "()"
    TBox a -> printStr "box " >> field (Right (-1)) a
    TPair a b -> do
      printStr "("
      field (Right 0) a
      printStr ", "
      field (Right 1) b
      printStr ")"
    TData d tys | Just (ps, cs) <- dataOf decls d -> do
      let inst = substTy (M.fromList (zip ps tys)) M.empty
      layouts <- gets gsLayouts
      -- As in "Keel.AArch64": constructors never built at this type have no block to print.
      let built = [(c, fts, lid, h, ws) | (c, fs) <- cs, let fts = map inst fs, let (key, h, ws) = dataLayoutKey (conNumbers decls M.! c) fts, Just lid <- [M.lookup key layouts]]
      lDone <- newLabel
      labels <- mapM (const newLabel) built
      ins ("mov r11, " ++ mem "rsp" 0)
      ins ("mov r11d, " ++ mem32 "r11" (-8))
      ins "and r11d, 0x3ff"
      forM_ (zip built labels) $ \((_, _, lid, _, _), l) -> do
        ins ("cmp r11d, " ++ show lid)
        ins ("je " ++ l)
      ins ("jmp " ++ lDone)
      forM_ (zip built labels) $ \((c, fts, _, h, ws), l) -> do
        line (l ++ ":")
        printStr c
        unless (null fts) $ do
          printStr "("
          forM_ (zip [0 :: Int ..] fts) $ \(i, ft) -> do
            when (i > 0) $ printStr ", "
            field (if h == Just i then Left (case ft of TInt it -> signed it; _ -> False) else Right (fromMaybe i (elemIndex i ws))) ft
          printStr ")"
        ins ("jmp " ++ lDone)
      line (lDone ++ ":")
    TData "Array" [a] -> do
      lLoop <- newLabel
      lFirst <- newLabel
      lDone <- newLabel
      printStr "["
      ins ("mov " ++ mem "rsp" 8 ++ ", 0")
      line (lLoop ++ ":")
      ins ("mov r11, " ++ mem "rsp" 0)
      ins ("mov r10, " ++ mem "rsp" 8)
      ins ("cmp r10, " ++ mem "r11" 0)
      ins ("jae " ++ lDone)
      ins "test r10, r10"
      ins ("jz " ++ lFirst)
      printStr ", "
      line (lFirst ++ ":")
      ins ("mov r11, " ++ mem "rsp" 0)
      ins ("mov r10, " ++ mem "rsp" 8)
      element (elemOf a)
      maybe (printStr "...") (\(_, l) -> ins ("call " ++ l)) (M.lookup (prettyTy a) printers)
      ins ("inc " ++ mem "rsp" 8)
      ins ("jmp " ++ lLoop)
      line (lDone ++ ":")
      printStr "]"
    TData _ _ -> printStr "<codata>"
    _ -> printStr "<closure>"
  ins "mov rsp, rbp"
  ins "pop rbp"
  ins "ret"
  where
    -- Print word i of the block (-1: the value itself), or its header field (Left: whether
    -- signed), with its type's printer.
    field :: Either Bool Int -> Ty -> G ()
    field place ft = do
      ins ("mov rax, " ++ mem "rsp" 0)
      case place of
        Left sgn -> ins (narrowLoad sgn "rax" ++ mem32 "rax" (-4))
        Right i -> when (i >= 0) $ ins ("mov rax, " ++ mem "rax" (8 * i))
      case M.lookup (prettyTy ft) printers of
        Just (_, l) -> ins ("call " ++ l)
        Nothing -> printStr "..."

-- | C's main: reserve the heap, run the Keel main, print its result as a last line, drop it,
-- and with KEEL_STATS set report the allocator counters on stderr.
emitEntry :: M.Map String (Ty, String) -> Ty -> G ()
emitEntry printers t = do
  line "\t.globl main"
  line "\t.p2align 4"
  line "main:"
  ins "push rbp"
  ins "mov rbp, rsp"
  ins "sub rsp, 64"
  -- mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0)
  ins "xor edi, edi"
  li "rsi" heapReserve
  ins "mov edx, 3"
  ins "mov ecx, 0x4022"
  ins "mov r8, -1"
  ins "xor r9d, r9d"
  ins "call mmap"
  ins "cmp rax, -1"
  ins "je _keel_panic_oom"
  ins "mov qword ptr [rip + _keel_heap_ptr], rax"
  li "r11" heapReserve
  ins "add rax, r11"
  ins "mov qword ptr [rip + _keel_heap_ptr + 8], rax"
  ins "xor eax, eax"
  ins "call _kf_main"
  ins ("mov " ++ mem "rsp" 48 ++ ", rax")
  printStr "result: "
  ins ("mov rax, " ++ mem "rsp" 48)
  forM_ (M.lookup (prettyTy t) printers) $ \(_, l) -> ins ("call " ++ l)
  printStr "\n"
  when (isPtr t) $ ins ("mov rax, " ++ mem "rsp" 48) >> ins "call _keel_drop"
  lNoStats <- newLabel
  name <- str "KEEL_STATS"
  address "rdi" name
  ins "call getenv"
  ins "test rax, rax"
  ins ("jz " ++ lNoStats)
  -- dprintf(2, fmt, allocs, recycled, in-place, freed, live): live is the 7th argument, on the stack
  ins "mov rdx, qword ptr [rip + _keel_stats]"
  ins "mov rcx, qword ptr [rip + _keel_stats + 8]"
  ins "mov r8, qword ptr [rip + _keel_stats + 16]"
  ins "mov r9, qword ptr [rip + _keel_stats + 24]"
  ins "mov rax, rdx"
  ins "add rax, rcx"
  ins "add rax, r8"
  ins "sub rax, r9"
  ins ("mov " ++ mem "rsp" 0 ++ ", rax")
  ins "mov edi, 2"
  fmt <- str "keel-stats: allocs=%lld recycled=%lld inplace=%lld freed=%lld live=%lld\n"
  address "rsi" fmt
  ins "xor eax, eax"
  ins "call dprintf"
  line (lNoStats ++ ":")
  ins "xor eax, eax"
  ins "mov rsp, rbp"
  ins "pop rbp"
  ins "ret"

-- Runtime ---------------------------------------------------------------------------------

-- | The runtime, as in "Keel.AArch64" (spec/memory.md). Its routines take rax, rdi, rsi (Keel's
-- convention) and keep the stack 16-byte aligned at their calls.
emitRuntime :: G ()
emitRuntime = do
  -- _keel_alloc: rax = payload words, rdi = header without its count → rax = payload.
  -- Clobbers rcx, rdx, rsi, rdi only.
  fn "_keel_alloc"
  ins ("cmp rax, " ++ show maxSmall)
  ins "ja .L_alloc_bump"
  -- The free lists, or an empty table while an arena is open: then everything comes from the
  -- bump pointer, so all of it lies above the arena's start and goes when it closes.
  ins "mov rcx, qword ptr [rip + _keel_fl]"
  ins "mov rdx, qword ptr [rcx + rax*8]"
  ins "test rdx, rdx"
  ins "jz .L_alloc_bump"
  ins "test rax, rax"
  ins "jz .L_alloc_link0"
  ins "mov rsi, qword ptr [rdx]" -- the next free block
  line ".L_alloc_pop:"
  ins "mov qword ptr [rcx + rax*8], rsi"
  ins "inc qword ptr [rip + _keel_stats + 8]"
  ins "jmp .L_alloc_header"
  line ".L_alloc_bump:"
  address "rsi" "_keel_heap_ptr"
  ins "mov rdx, qword ptr [rsi]"
  ins "lea rcx, [rdx + rax*8 + 8]"
  ins "cmp rcx, qword ptr [rsi + 8]"
  ins "ja _keel_panic_oom"
  ins "mov qword ptr [rsi], rcx"
  ins "add rdx, 8"
  ins "inc qword ptr [rip + _keel_stats]"
  line ".L_alloc_header:"
  ins "or rdi, 1024" -- count 1
  ins "mov qword ptr [rdx - 8], rdi"
  ins "mov rax, rdx"
  ins "ret"
  -- A block of no words links to the next in its header's high half, in words from it.
  line ".L_alloc_link0:"
  ins "movsxd rsi, dword ptr [rdx - 4]"
  ins "test rsi, rsi"
  ins "jz .L_alloc_pop"
  ins "lea rsi, [rdx + rsi*8]"
  ins "jmp .L_alloc_pop"

  -- Arenas: a record [base before, enclosing record, allocations so far] from the bump
  -- pointer; closing resets the bump pointer to it.
  fn "_keel_arena_open"
  address "rcx" "_keel_heap_ptr"
  ins "mov rdx, qword ptr [rcx]" -- the record
  ins "lea rsi, [rdx + 24]"
  ins "cmp rsi, qword ptr [rcx + 8]"
  ins "ja _keel_panic_oom"
  ins "mov qword ptr [rcx], rsi"
  address "rcx" "_keel_arena_base"
  ins "mov rsi, qword ptr [rcx]"
  ins "mov qword ptr [rdx], rsi"
  address "rdi" "_keel_arena_top"
  ins "mov rax, qword ptr [rdi]"
  ins "mov qword ptr [rdx + 8], rax"
  ins "mov qword ptr [rdi], rdx"
  ins "mov rax, qword ptr [rip + _keel_stats]"
  ins "mov qword ptr [rdx + 16], rax"
  ins "cmp rsi, rdx"
  ins "jb .L_arena_keep"
  ins "mov qword ptr [rcx], rdx"
  line ".L_arena_keep:"
  address "rcx" "_keel_nofree"
  ins "mov qword ptr [rip + _keel_fl], rcx"
  ins "xor eax, eax"
  ins "ret"

  fn "_keel_arena_close"
  address "rdi" "_keel_arena_top"
  ins "mov rdx, qword ptr [rdi]" -- the record
  ins "mov rsi, qword ptr [rdx + 8]"
  ins "mov qword ptr [rdi], rsi"
  ins "mov rsi, qword ptr [rdx]"
  ins "mov qword ptr [rip + _keel_arena_base], rsi"
  ins "cmp rsi, -1" -- the outermost arena closed: the free lists are back
  ins "jne .L_close_inner"
  address "rcx" "_keel_freelists"
  ins "mov qword ptr [rip + _keel_fl], rcx"
  line ".L_close_inner:"
  ins "mov rcx, qword ptr [rip + _keel_stats]"
  ins "sub rcx, qword ptr [rdx + 16]" -- allocated inside: freed now
  ins "add qword ptr [rip + _keel_stats + 24], rcx"
  ins "mov rsi, qword ptr [rdx + 8]" -- … and not again when the enclosing arena closes
  ins "test rsi, rsi"
  ins "jz .L_close_outermost"
  ins "add qword ptr [rsi + 16], rcx"
  line ".L_close_outermost:"
  ins "mov qword ptr [rip + _keel_heap_ptr], rdx"
  ins "xor eax, eax"
  ins "ret"

  -- _keel_drop: rax = block. Decrement; at zero, drop the children and free the block. The
  -- last pointer child is handled by looping, so dropping a long list uses constant stack.
  fn "_keel_drop"
  ins "push rbx"
  ins "push r12"
  ins "sub rsp, 8"
  line ".L_drop_top:"
  ins "mov ecx, dword ptr [rax - 8]"
  ins "test ecx, ecx"
  ins "js .L_drop_ret"
  ins "sub ecx, 1024"
  ins "js _keel_panic_rc" -- the count was 0: a freed block
  ins "mov dword ptr [rax - 8], ecx"
  ins "test ecx, 0x7ffffc00"
  ins "jnz .L_drop_ret"
  ins "cmp rax, qword ptr [rip + _keel_arena_base]"
  ins "jae .L_drop_ret" -- in an open arena: freed when it closes
  ins "inc qword ptr [rip + _keel_stats + 24]"
  ins "mov rbx, rax"
  ins "and ecx, 0x3ff"
  ins ("cmp ecx, " ++ show arrayLayout)
  ins "jae .L_drop_special"
  ins "mov r12, qword ptr [rax - 8]"
  ins "shl r12, 8"
  ins "shr r12, 48" -- the pointer map, bits 40–55
  line ".L_drop_loop:"
  ins "test r12, r12"
  ins "jz .L_drop_free"
  ins "lea rdx, [r12 - 1]"
  ins "and rdx, r12"
  ins "jz .L_drop_last" -- one pointer child left
  ins "bsf rcx, r12"
  ins "btr r12, rcx"
  ins "mov rax, qword ptr [rbx + rcx*8]"
  ins "call _keel_drop"
  ins "jmp .L_drop_loop"
  line ".L_drop_last:"
  ins "bsf rcx, r12"
  ins "mov r12, qword ptr [rbx + rcx*8]"
  ins "mov rax, rbx"
  ins "call _keel_free_block"
  ins "mov rax, r12"
  ins "jmp .L_drop_top"
  line ".L_drop_free:"
  ins "mov rax, rbx"
  ins "call _keel_free_block"
  line ".L_drop_ret:"
  ins "add rsp, 8"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"
  -- A block with a field in its header: its pointer map is in the table.
  line ".L_drop_special:"
  ins ("cmp ecx, " ++ show fieldLayouts)
  ins "jb .L_drop_array"
  address "rdx" "_keel_layouts"
  ins ("mov r12d, dword ptr [rdx + rcx*4 - " ++ show (4 * fieldLayouts) ++ "]")
  ins "shr r12d, 8"
  ins "jmp .L_drop_loop"
  -- An array: drop its elements if they are pointers, last first, then free it.
  line ".L_drop_array:"
  ins ("cmp ecx, " ++ show (arrayLayout + 2))
  ins "jne .L_drop_free"
  ins "mov r12, qword ptr [rbx]"
  line ".L_drop_elems:"
  ins "test r12, r12"
  ins "jz .L_drop_free"
  ins "dec r12"
  ins "mov rax, qword ptr [rbx + r12*8 + 16]"
  ins "call _keel_drop"
  ins "jmp .L_drop_elems"

  -- _keel_free_block: rax = block with count 0 → its size's free list. Clobbers rcx, rdx, rsi.
  fn "_keel_free_block"
  ins "movzx ecx, byte ptr [rax - 4]" -- its words (an array's: capped at 255)
  ins ("test dword ptr [rax - 8], " ++ show fieldLayouts) -- the header holds a field
  ins "jz .L_free_size"
  ins "mov edx, dword ptr [rax - 8]"
  ins "and edx, 0x1ff"
  address "rsi" "_keel_layouts"
  ins "movzx ecx, byte ptr [rsi + rdx*4]"
  line ".L_free_size:"
  ins ("cmp rcx, " ++ show maxSmall)
  ins "ja .L_free_ret" -- ponytail: large blocks are not recycled
  address "rsi" "_keel_freelists"
  ins "mov rdx, qword ptr [rsi + rcx*8]"
  ins "test rcx, rcx"
  ins "jz .L_free_link0"
  ins "mov qword ptr [rax], rdx" -- the link, in the first word
  ins "mov qword ptr [rsi + rcx*8], rax"
  line ".L_free_ret:"
  ins "ret"
  -- A block of no words: the link in its header's high half, in words from it (0: none).
  line ".L_free_link0:"
  ins "test rdx, rdx"
  ins "jz .L_free_link"
  ins "sub rdx, rax"
  ins "sar rdx, 3"
  line ".L_free_link:"
  ins "mov dword ptr [rax - 4], edx"
  ins "mov qword ptr [rsi], rax"
  ins "ret"

  -- _keel_drop_reuse: rax = block → rax = the block if it was unique (its children dropped,
  -- count 0 until reused), or 0 after an ordinary decrement.
  fn "_keel_drop_reuse"
  ins "push rbx"
  ins "push r12"
  ins "sub rsp, 8"
  ins "mov ecx, dword ptr [rax - 8]"
  ins "test ecx, ecx"
  ins "js .L_reuse_none"
  ins "mov edx, ecx"
  ins "shr edx, 10"
  ins "jz _keel_panic_rc"
  ins "cmp edx, 1"
  ins "jne .L_reuse_shared"
  ins "inc qword ptr [rip + _keel_stats + 24]"
  ins "mov rbx, rax"
  ins "mov r12, qword ptr [rax - 8]"
  ins "shl r12, 8"
  ins "shr r12, 48" -- the pointer map
  ins ("test ecx, " ++ show fieldLayouts)
  ins "jz .L_reuse_loop"
  ins "and ecx, 0x3ff" -- a field in the header: the map is in the table
  address "rdx" "_keel_layouts"
  ins ("mov r12d, dword ptr [rdx + rcx*4 - " ++ show (4 * fieldLayouts) ++ "]")
  ins "shr r12d, 8"
  line ".L_reuse_loop:"
  ins "test r12, r12"
  ins "jz .L_reuse_done"
  ins "bsf rcx, r12"
  ins "btr r12, rcx"
  ins "mov rax, qword ptr [rbx + rcx*8]"
  ins "call _keel_drop"
  ins "jmp .L_reuse_loop"
  line ".L_reuse_done:"
  ins "mov rax, rbx"
  ins "and dword ptr [rax - 8], 0x3ff" -- count 0 until reused
  ins "jmp .L_reuse_ret"
  line ".L_reuse_shared:"
  ins "sub ecx, 1024"
  ins "mov dword ptr [rax - 8], ecx"
  line ".L_reuse_none:"
  ins "xor eax, eax"
  line ".L_reuse_ret:"
  ins "add rsp, 8"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- Arrays (spec/memory.md): payload [length, capacity, elements…]; the layout is arrayLayout
  -- plus the kind: 0 for 4-byte elements, 1 words, 2 pointers. An update to an array nothing
  -- else references happens in place; otherwise the array is copied first.

  -- _keel_array_alloc: rax = capacity, rdi = kind → rax = an empty array.
  fn "_keel_array_alloc"
  ins "push rbx"
  ins "push r12"
  ins "sub rsp, 8"
  ins "mov rbx, rax"
  ins "mov r12, rdi"
  ins "xor ecx, ecx"
  ins "test rdi, rdi"
  ins "setnz cl"
  elemWords "rax" "rbx"
  ins "mov qword ptr [rsp], rax"
  ins "xor edi, edi"
  ins "call _keel_alloc"
  ins "mov rcx, qword ptr [rsp]" -- its words, capped at 255
  ins "mov edx, 255"
  ins "cmp rcx, rdx"
  ins "cmova rcx, rdx"
  ins "shl rcx, 32"
  ins ("lea rdx, [r12 + " ++ show (1024 + arrayLayout) ++ "]") -- count 1, the kind's layout
  ins "or rdx, rcx"
  ins "mov qword ptr [rax - 8], rdx"
  ins "mov qword ptr [rax], 0"
  ins "mov qword ptr [rax + 8], rbx"
  ins "add rsp, 8"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- _keel_array_new: rax = length, rdi = the element (owned), rsi = kind → rax.
  fn "_keel_array_new"
  ins "push rbx"
  ins "push r12"
  ins "push r13"
  ins "push r14"
  ins "sub rsp, 8"
  ins "test rax, rax"
  ins "js _keel_panic_bounds"
  ins "mov rbx, rax"
  ins "mov r12, rdi"
  ins "mov r13, rsi"
  ins "mov rdi, rsi"
  ins "call _keel_array_alloc"
  ins "mov qword ptr [rax], rbx"
  ins "xor ecx, ecx"
  ins "test r13, r13"
  ins "jz .L_anew_fill4"
  line ".L_anew_fill:"
  ins "cmp rcx, rbx"
  ins "jae .L_anew_filled"
  ins "mov qword ptr [rax + rcx*8 + 16], r12"
  ins "inc rcx"
  ins "jmp .L_anew_fill"
  line ".L_anew_fill4:"
  ins "cmp rcx, rbx"
  ins "jae .L_anew_filled"
  ins "mov dword ptr [rax + rcx*4 + 16], r12d"
  ins "inc rcx"
  ins "jmp .L_anew_fill4"
  line ".L_anew_filled:"
  ins "cmp r13, 2"
  ins "jne .L_anew_ret"
  -- The element now has n references in the array; the caller gave one.
  ins "test rbx, rbx"
  ins "jz .L_anew_drop"
  ins "mov edx, dword ptr [r12 - 8]"
  ins "test edx, edx"
  ins "js .L_anew_ret"
  ins "mov ecx, edx"
  ins "shr ecx, 10"
  ins "lea rcx, [rcx + rbx - 1]"
  ins "and edx, 0x3ff"
  ins "cmp rcx, 0x1fffff"
  ins "jbe .L_anew_count"
  ins "or edx, 0x80000000" -- the count overflowed: immortal
  ins "jmp .L_anew_store"
  line ".L_anew_count:"
  ins "shl ecx, 10"
  ins "or edx, ecx"
  line ".L_anew_store:"
  ins "mov dword ptr [r12 - 8], edx"
  ins "jmp .L_anew_ret"
  line ".L_anew_drop:"
  ins "mov r14, rax"
  ins "mov rax, r12"
  ins "call _keel_drop"
  ins "mov rax, r14"
  line ".L_anew_ret:"
  ins "add rsp, 8"
  ins "pop r14"
  ins "pop r13"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- _keel_array_clone: rax = array (owned), rdi = capacity ≥ its length → rax = a fresh array
  -- with the same elements. A unique array's elements move and its block is freed; a shared
  -- one's are duplicated and its count decremented.
  fn "_keel_array_clone"
  ins "push rbx"
  ins "push r12"
  ins "push r13"
  ins "push r14"
  ins "sub rsp, 8"
  ins "mov rbx, rax"
  ins "mov ecx, dword ptr [rax - 8]"
  ins "and ecx, 0x3ff"
  ins ("sub ecx, " ++ show arrayLayout) -- the kind
  ins "mov r13, rcx"
  ins "mov rax, rdi"
  ins "mov rdi, rcx"
  ins "call _keel_array_alloc"
  ins "mov r12, rax"
  ins "mov r14, qword ptr [rbx]"
  ins "mov qword ptr [r12], r14"
  -- Copy the elements' words.
  ins "xor ecx, ecx"
  ins "test r13, r13"
  ins "setnz cl"
  elemWords "rdx" "r14"
  ins "sub rdx, 2"
  ins "xor ecx, ecx"
  line ".L_aclone_copy:"
  ins "cmp rcx, rdx"
  ins "jae .L_aclone_copied"
  ins "mov rsi, qword ptr [rbx + rcx*8 + 16]"
  ins "mov qword ptr [r12 + rcx*8 + 16], rsi"
  ins "inc rcx"
  ins "jmp .L_aclone_copy"
  line ".L_aclone_copied:"
  ins "mov ecx, dword ptr [rbx - 8]"
  ins "mov edx, ecx"
  ins "shr edx, 10"
  ins "cmp edx, 1"
  ins "jne .L_aclone_shared"
  ins "and ecx, 0x3ff" -- count 0
  ins "mov dword ptr [rbx - 8], ecx"
  ins "cmp rbx, qword ptr [rip + _keel_arena_base]"
  ins "jae .L_aclone_ret" -- in an open arena: freed when it closes
  ins "inc qword ptr [rip + _keel_stats + 24]"
  ins "mov rax, rbx"
  ins "call _keel_free_block"
  ins "jmp .L_aclone_ret"
  line ".L_aclone_shared:"
  ins "cmp r13, 2"
  ins "jne .L_aclone_dec"
  ins "xor ecx, ecx"
  line ".L_aclone_dup:"
  ins "cmp rcx, r14"
  ins "jae .L_aclone_dec"
  ins "mov rdx, qword ptr [rbx + rcx*8 + 16]"
  ins "mov esi, dword ptr [rdx - 8]"
  ins "test esi, esi"
  ins "js .L_aclone_next"
  ins "add esi, 1024"
  ins "mov dword ptr [rdx - 8], esi"
  line ".L_aclone_next:"
  ins "inc rcx"
  ins "jmp .L_aclone_dup"
  line ".L_aclone_dec:"
  ins "sub dword ptr [rbx - 8], 1024"
  line ".L_aclone_ret:"
  ins "mov rax, r12"
  ins "add rsp, 8"
  ins "pop r14"
  ins "pop r13"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- _keel_array_set: rax = array (owned), rdi = index, rsi = element (owned) → rax.
  fn "_keel_array_set"
  ins "push rbx"
  ins "push r12"
  ins "push r13"
  ins "cmp rdi, qword ptr [rax]"
  ins "jae _keel_panic_bounds"
  ins "mov rbx, rdi"
  ins "mov r12, rsi"
  ins "mov ecx, dword ptr [rax - 8]"
  ins "shr ecx, 10"
  ins "cmp ecx, 1"
  ins "je .L_aset_store"
  ins "mov rdi, qword ptr [rax + 8]"
  ins "call _keel_array_clone"
  line ".L_aset_store:"
  ins "mov ecx, dword ptr [rax - 8]"
  ins "and ecx, 0x3ff"
  ins ("cmp ecx, " ++ show arrayLayout)
  ins "jne .L_aset_word"
  ins "mov dword ptr [rax + rbx*4 + 16], r12d"
  ins "jmp .L_aset_ret"
  line ".L_aset_word:"
  ins "mov r13, qword ptr [rax + rbx*8 + 16]"
  ins "mov qword ptr [rax + rbx*8 + 16], r12"
  ins ("cmp ecx, " ++ show (arrayLayout + 2))
  ins "jne .L_aset_ret"
  ins "mov r12, rax"
  ins "mov rax, r13"
  ins "call _keel_drop" -- the element it replaced
  ins "mov rax, r12"
  line ".L_aset_ret:"
  ins "pop r13"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- _keel_array_push: rax = array (owned), rdi = element (owned) → rax. A full array doubles:
  -- in place when it is unique and the last block before the bump pointer (then nothing lies
  -- after it, not even an arena's record), otherwise into a copy.
  fn "_keel_array_push"
  ins "push rbx"
  ins "push r12"
  ins "sub rsp, 8"
  ins "mov rbx, rdi"
  ins "mov rcx, qword ptr [rax]"
  ins "cmp rcx, qword ptr [rax + 8]"
  ins "jae .L_apush_grow"
  ins "mov edx, dword ptr [rax - 8]"
  ins "shr edx, 10"
  ins "cmp edx, 1"
  ins "je .L_apush_store"
  ins "mov rdi, qword ptr [rax + 8]"
  ins "call _keel_array_clone"
  ins "jmp .L_apush_store"
  line ".L_apush_grow:"
  ins "mov rdi, qword ptr [rax + 8]"
  ins "shl rdi, 1"
  ins "mov edx, 4"
  ins "cmp rdi, rdx"
  ins "cmovb rdi, rdx"
  ins "mov edx, dword ptr [rax - 8]"
  ins "shr edx, 10"
  ins "cmp edx, 1"
  ins "jne .L_apush_copy"
  ins "mov edx, dword ptr [rax - 8]"
  ins "and edx, 0x3ff"
  ins "xor ecx, ecx"
  ins ("cmp edx, " ++ show arrayLayout)
  ins "setne cl"
  elemWords "rsi" "qword ptr [rax + 8]"
  ins "lea rsi, [rax + rsi*8]" -- the block's end
  address "rdx" "_keel_heap_ptr"
  ins "cmp rsi, qword ptr [rdx]"
  ins "jne .L_apush_copy"
  elemWords "rsi" "rdi"
  ins "lea r12, [rax + rsi*8]"
  ins "cmp r12, qword ptr [rdx + 8]"
  ins "ja _keel_panic_oom"
  ins "mov qword ptr [rdx], r12"
  ins "mov qword ptr [rax + 8], rdi"
  ins "mov edx, 255" -- the header's words, capped at 255
  ins "cmp rsi, rdx"
  ins "cmova rsi, rdx"
  ins "mov byte ptr [rax - 4], sil"
  ins "jmp .L_apush_store"
  line ".L_apush_copy:"
  ins "call _keel_array_clone"
  line ".L_apush_store:"
  ins "mov rcx, qword ptr [rax]"
  ins "mov edx, dword ptr [rax - 8]"
  ins "and edx, 0x3ff"
  ins ("cmp edx, " ++ show arrayLayout)
  ins "jne .L_apush_word"
  ins "mov dword ptr [rax + rcx*4 + 16], ebx"
  ins "jmp .L_apush_count"
  line ".L_apush_word:"
  ins "mov qword ptr [rax + rcx*8 + 16], rbx"
  line ".L_apush_count:"
  ins "inc rcx"
  ins "mov qword ptr [rax], rcx"
  ins "add rsp, 8"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- _keel_array_pop: rax = array (owned) → rax without its last element.
  fn "_keel_array_pop"
  ins "push rbx"
  ins "push r12"
  ins "sub rsp, 8"
  ins "cmp qword ptr [rax], 0"
  ins "je _keel_panic_bounds"
  ins "mov edx, dword ptr [rax - 8]"
  ins "shr edx, 10"
  ins "cmp edx, 1"
  ins "je .L_apop_take"
  ins "mov rdi, qword ptr [rax + 8]"
  ins "call _keel_array_clone"
  line ".L_apop_take:"
  ins "mov rcx, qword ptr [rax]"
  ins "dec rcx"
  ins "mov qword ptr [rax], rcx"
  ins "mov edx, dword ptr [rax - 8]"
  ins "and edx, 0x3ff"
  ins ("cmp edx, " ++ show (arrayLayout + 2))
  ins "jne .L_apop_ret"
  ins "mov rbx, rax"
  ins "mov rax, qword ptr [rax + rcx*8 + 16]"
  ins "call _keel_drop"
  ins "mov rax, rbx"
  line ".L_apop_ret:"
  ins "add rsp, 8"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- _keel_perform: rax = operation number, rdi = argument (owned) → rax = result. Finds the
  -- innermost frame handling the operation and calls its clause with the frames outside it
  -- installed; unhandled operations go to the machine.
  fn "_keel_perform"
  ins "push rbx"
  ins "push r12"
  ins "push r13"
  ins "mov r12, qword ptr [rip + _keel_handlers]" -- restored afterwards
  ins "mov rcx, r12"
  line ".L_perform_frame:"
  ins "test rcx, rcx"
  ins "jz .L_perform_machine"
  ins "mov rdx, qword ptr [rcx + 8]" -- clauses in this frame
  ins "lea rsi, [rcx + 16]"
  line ".L_perform_scan:"
  ins "test rdx, rdx"
  ins "jz .L_perform_next"
  ins "cmp qword ptr [rsi], rax"
  ins "je .L_perform_found"
  ins "add rsi, 16"
  ins "dec rdx"
  ins "jmp .L_perform_scan"
  line ".L_perform_next:"
  ins "mov rcx, qword ptr [rcx]"
  ins "jmp .L_perform_frame"
  line ".L_perform_found:"
  ins "mov rdx, qword ptr [rcx]"
  ins "mov qword ptr [rip + _keel_handlers], rdx" -- the clause runs under the enclosing frames
  ins "mov rax, qword ptr [rsi + 8]"
  -- the call consumes the closure, but the frame keeps it: duplicate first
  ins "mov edx, dword ptr [rax - 8]"
  ins "test edx, edx"
  ins "js .L_perform_call"
  ins "add edx, 1024"
  ins "mov dword ptr [rax - 8], edx"
  line ".L_perform_call:"
  ins "call qword ptr [rax]"
  ins "mov qword ptr [rip + _keel_handlers], r12"
  ins "jmp .L_perform_ret"
  -- The machine, through the C library: out (0) and putc (1) print, getc (2) reads stdin,
  -- files (7–9); MMIO (3–6) needs a freestanding target.
  line ".L_perform_machine:"
  ins "cmp rax, 1"
  ins "je .L_perform_putc"
  ins "cmp rax, 2"
  ins "je .L_perform_getc"
  ins "cmp rax, 7"
  ins "je .L_perform_open"
  ins "cmp rax, 8"
  ins "je .L_perform_read"
  ins "cmp rax, 9"
  ins "je .L_perform_close"
  ins "test rax, rax"
  ins "jnz _keel_panic_unhandled"
  ins "mov rsi, rdi"
  fmt <- str "%lld\n"
  address "rdi" fmt
  ins "xor eax, eax"
  ins "call printf"
  ins "xor eax, eax"
  ins "jmp .L_perform_ret"
  line ".L_perform_putc:"
  ins "call putchar"
  ins "xor eax, eax"
  ins "jmp .L_perform_ret"
  line ".L_perform_getc:"
  ins "call getchar" -- a byte, or EOF (-1)
  ins "cdqe"
  ins "jmp .L_perform_ret"
  -- openFile: rdi = the path, an Array u8 (owned). Copy it to the stack with a NUL, fopen it,
  -- and drop the array. The handle is the FILE pointer, or -1.
  line ".L_perform_open:"
  ins "mov rbx, rdi"
  ins "mov rcx, qword ptr [rdi]"
  ins "mov r13, rsp"
  ins "lea rdx, [rcx + 16]"
  ins "and rdx, -16"
  ins "sub rsp, rdx"
  ins "xor edx, edx"
  line ".L_open_copy:"
  ins "cmp rdx, rcx"
  ins "jae .L_open_copied"
  ins "mov esi, dword ptr [rbx + rdx*4 + 16]" -- 4-byte elements
  ins "mov byte ptr [rsp + rdx], sil"
  ins "inc rdx"
  ins "jmp .L_open_copy"
  line ".L_open_copied:"
  ins "mov byte ptr [rsp + rcx], 0"
  ins "mov rdi, rsp"
  mode <- str "rb"
  address "rsi" mode
  ins "call fopen"
  ins "mov rsp, r13"
  ins "test rax, rax"
  ins "jnz .L_open_ok"
  ins "mov rax, -1"
  line ".L_open_ok:"
  ins "mov r12, rax" -- (the handlers were not touched: r12 is free here)
  ins "mov rax, rbx"
  ins "call _keel_drop"
  ins "mov rax, r12"
  ins "jmp .L_perform_ret"
  line ".L_perform_read:"
  ins "call fgetc" -- a byte, or EOF (-1)
  ins "cdqe"
  ins "jmp .L_perform_ret"
  line ".L_perform_close:"
  ins "call fclose"
  ins "xor eax, eax"
  line ".L_perform_ret:"
  ins "pop r13"
  ins "pop r12"
  ins "pop rbx"
  ins "ret"

  -- Output through printf, so it shares stdout's buffer with the rest.
  printer "_keel_print_str" "%s" -- rax = NUL-terminated string
  printer "_keel_print_i64" "%lld"
  printer "_keel_print_u64" "%llu"

  panic "_keel_panic_unhandled" "panic: unhandled operation (MMIO needs a freestanding target)\n"
  panic "_keel_panic_div" "panic: division by zero\n"
  panic "_keel_panic_bounds" "panic: array index out of bounds\n"
  panic "_keel_panic_overflow" "panic: arithmetic overflow\n"
  panic "_keel_panic_oom" "panic: out of memory\n"
  panic "_keel_panic_rc" "panic: reference count error\n"
  where
    fn lbl = line "\t.p2align 4" >> line (lbl ++ ":")
    -- An array's payload words for n elements into d: (n << (2 + cl) + 23) >> 3, with cl 1 for
    -- 8-byte elements (2 + the elements, rounded up to words).
    elemWords d n = do
      ins ("mov " ++ d ++ ", " ++ n)
      ins "add cl, 2"
      ins ("shl " ++ d ++ ", cl")
      ins "sub cl, 2"
      ins ("add " ++ d ++ ", 23")
      ins ("shr " ++ d ++ ", 3")
    printer lbl fmtText = do
      fn lbl
      ins "sub rsp, 8"
      ins "mov rsi, rax"
      l <- str fmtText
      address "rdi" l
      ins "xor eax, eax"
      ins "call printf"
      ins "add rsp, 8"
      ins "ret"
    panic lbl msg = do
      l <- str msg
      fn lbl
      ins "and rsp, -16"
      ins "mov edi, 2"
      address "rsi" l
      ins ("mov edx, " ++ show (length msg))
      ins "call write"
      ins "mov edi, 101"
      ins "call exit"
