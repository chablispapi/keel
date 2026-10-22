-- | Code generator: the lowered IR ("Keel.Lower") → Apple ARM64 assembly (Mach-O), assembled
-- and linked with the system @cc@ (notes.md §12, §17).
--
-- Deliberately simple: every variable lives in a stack slot and values pass through scratch
-- registers x9–x17, so nothing needs saving across calls.
-- A call in tail position reuses the frame, and a function calling itself there jumps back
-- to where it stores its arguments, so loops written as tail recursion are loops.
--
-- Conventions: every function is called with its closure (or codata block) in x0 and its
-- argument in x1, both owned, and returns an owned result in x0. Heap blocks carry a header
-- word at offset -8 (reference count, size, tag, pointer map) and are recycled through free lists
-- (spec/memory.md). Panics exit with status 101 after flushing stdout.
module Keel.AArch64 (compileNative, compileNativeWith, compileNativeWithReuse, emitProgram, prepare, bound, uses, printerTypes, dataOf, header, heapSize, maxSmall, Loc (..), allocate, template, Reduction (..), reduction) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.List (elemIndex, nub, sortOn)
import Data.ByteString qualified as B
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Numeric (showOct)
import Keel.Check (checkProgram)
import Keel.Lower
import Keel.Range (ranges)
import Keel.Mono (compileWith)
import Keel.Syntax

-- | The whole pipeline: check, elaborate, monomorphize, lower, emit.
compileNative :: Program -> Either String String
compileNative = compileNativeWith False

-- | With @debug@, the assembly carries a line table (.file/.loc) for @cc -g@.
compileNativeWith :: Bool -> Program -> Either String String
compileNativeWith debug = compileNativeWithReuse debug True

-- | Test/benchmark control: debug information, then inline full-field reuse. Disabling
-- reuse specialization retains the same lowering, ownership decisions and runtime helper.
compileNativeWithReuse :: Bool -> Bool -> Program -> Either String String
compileNativeWithReuse debug reuse p = do
  (decls, t, lp) <- prepareWith debug p
  pure (emitProgramWithReuse reuse decls t lp)

-- | The target-independent part of every back end: the core pipeline and lowering. Returns
-- the declarations (with built-ins), @main@'s type, and the lowered program.
prepare :: Program -> Either String ([Decl], Ty, LProg)
prepare = prepareWith False

prepareWith :: Bool -> Program -> Either String ([Decl], Ty, LProg)
prepareWith debug p = do
  mono <- either (Left . show) Right (compileWith debug p)
  (t, _) <- either (Left . show) Right (checkProgram mono)
  lp <- ranges <$> lower mono
  let Program decls _ = mono
  pure (optionDecl : decls, t, lp)

heapSize :: Integer
heapSize = 64 * 1024 * 1024

-- | The native heap: address space only (zero-fill pages are mapped when first touched), so
-- it can be far larger than heapSize, which sizes the freestanding targets' RAM.
nativeHeapSize :: Integer
nativeHeapSize = 16 * 1024 * 1024 * 1024

-- | Blocks of up to this many payload words are recycled through free lists.
maxSmall :: Int
maxSmall = 64

-- | gsLocs: the line-table row (file number, line, column) for variables bound by a
-- positioned computation; empty unless the program kept positions (debug builds).
data GS = GS {gsLabel :: Int, gsLines :: [String], gsStrings :: M.Map String String, gsLocs :: M.Map String (Int, Int, Int), gsNullary :: S.Set Integer, gsLayouts :: M.Map (Integer, Int, Integer) Integer}

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
emitProgram = emitProgramWithReuse True

emitProgramWithReuse :: Bool -> [Decl] -> Ty -> LProg -> String
emitProgramWithReuse reuse decls mainTy (LProg funs statics mainF locs layouts) = unlines (reverse (gsLines (execState gen (GS 0 [] M.empty rows S.empty layouts))))
  where
    printers = printerTypes decls mainTy
    files = nub [f | (f, _, _) <- M.elems locs]
    rows = M.map (\(f, l, c) -> (maybe 0 (+ 1) (elemIndex f files), l, c)) locs
    gen = do
      line "\t.section __TEXT,__text,regular,pure_instructions"
      forM_ (zip [1 :: Int ..] files) $ \(n, f) -> ins (".file " ++ show n ++ " " ++ show f)
      forM_ (M.toList funs) $ \(i, f) -> emitFun reuse ("_kf_" ++ show i) f
      emitFun reuse "_kf_main" mainF
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
      tags <- gets gsNullary
      forM_ (S.toList tags) $ \t -> do
        ins (".quad " ++ show (header layouts t .|. 0x80000000) ++ "\t\t// header: immortal, layout " ++ show t)
        line ("_kn_" ++ show t ++ ":\t\t\t// every constructor without fields with this layout")
      layoutTable layouts
      line "_keel_heap_ptr:"
      ins ".quad _keel_heap"
      ins (".quad _keel_heap+" ++ show nativeHeapSize)
      -- The lowest open arena's start; all ones while none is open. And the innermost one.
      line "_keel_arena_base:"
      ins ".quad -1"
      line "_keel_arena_top:"
      ins ".quad 0"
      line "_keel_fl:"
      ins ".quad _keel_freelists"
      line ("\t.zerofill __DATA,__bss,_keel_freelists," ++ show (8 * (maxSmall + 1)) ++ ",3")
      line ("\t.zerofill __DATA,__bss,_keel_nofree," ++ show (8 * (maxSmall + 1)) ++ ",3")
      line "\t.zerofill __DATA,__bss,_keel_stats,32,3"
      line "\t.zerofill __DATA,__bss,_keel_handlers,8,3"
      -- Last, so the runtime's other data stays within adrp's ±4 GB of the code.
      line ("\t.zerofill __DATA,__bss,_keel_heap," ++ show nativeHeapSize ++ ",4")
      line "\t.section __TEXT,__cstring,cstring_literals"
      strs <- gets gsStrings
      forM_ (M.toList strs) $ \(s, l) -> line (l ++ ":\t.asciz " ++ show s)
      case files of
        f : _ -> debugInfo f ([("_kf_" ++ show i, funName fn) | (i, fn) <- M.toList funs] ++ [("_kf_main", "main")])
        [] -> pure ()

-- Functions -------------------------------------------------------------------------------

-- | Register allocation (M4): callee-saved registers, by graph colouring. Variables that are
-- live at the same time get different registers; most-used first, and a variable passed to a
-- self tail call prefers its parameter's register, so the back edge moves nothing. The rest
-- live in 8-byte stack slots. Every callee preserves these registers (Keel functions save what
-- they use; the runtime and the C library never touch them), so values survive calls.
-- Returns the locations, the (register, save offset) pairs and the frame size; the save area
-- follows the slots.
--
-- A register is written only after the instructions computing its value have read their
-- operands, or a variable could share one with an operand that dies there.
allocate :: [String] -> Fun -> [String] -> (M.Map String Loc, [(String, Int)], Int)
allocate calleeSaved (Fun _ params _ env _ _ body) vars0 =
  (M.fromList ([(v, InReg r) | (v, r) <- M.toList colours] ++ zip spilled (map InSlot [0 ..])), saved, frame)
  where
    vars = nub vars0
    counts = M.fromListWith (+) [(v, 1 :: Int) | v <- uses body ++ params ++ env]
    conflicts = interference (params ++ env) body
    -- Arguments of self tail calls: the parameter each would like to share a register with.
    prefs = M.fromListWith (++) (concat [[(a, [p]), (p, [a])] | Bind x (RCallKnown _ as) (Ret (AVar y)) <- subExprs body, x == y, length as == length params, (p, AVar a) <- zip params as])
    colours = foldl colour M.empty (sortOn (\v -> negate (M.findWithDefault 0 v counts)) vars)
    colour done v =
      let taken = S.fromList [r | w <- S.toList (M.findWithDefault S.empty v conflicts), Just r <- [M.lookup w done]]
          wanted = [r | p <- M.findWithDefault [] v prefs, Just r <- [M.lookup p done]]
       in case filter (`S.notMember` taken) (wanted ++ calleeSaved) of
            r : _ -> M.insert v r done
            [] -> done
    spilled = [v | v <- vars, v `M.notMember` colours]
    used = nub (M.elems colours)
    saved = [(r, 8 * (length spilled + i)) | (i, r) <- zip [0 ..] used]
    frame = 16 * ((8 * (length spilled + length used) + 15) `div` 16)

-- | Which variables are live at the same time: each variable defined, with the variables live
-- just after; the parameters and captured values all with each other.
interference :: [String] -> Expr -> M.Map String (S.Set String)
interference entry body = M.fromListWith S.union (concat [(x, ys) : [(y, S.singleton x) | y <- S.toList ys] | (x, ys) <- edges])
  where
    edges = [(p, S.fromList (filter (/= p) entry)) | p <- entry] ++ execState (live Nothing body) []
    def x after = modify ((x, S.delete x after) :) >> pure (S.delete x after)
    -- The variables live before an expression; join: the variable a branch's result goes to
    -- and what is live after the join.
    live :: Maybe (String, S.Set String) -> Expr -> State [(String, S.Set String)] (S.Set String)
    live join e = case e of
      Ret a -> case join of
        Nothing -> pure (atomSet a)
        Just (x, after) -> (<> atomSet a) <$> def x after
      Bind x rhs rest -> live join rest >>= def x >>= \s -> pure (s <> S.fromList (rhsUses rhs))
      BindIf x c a b rest -> do
        after <- live join rest
        la <- live (Just (x, after)) a
        lb <- live (Just (x, after)) b
        _ <- def x after
        pure (atomSet c <> la <> lb)
      BindCase x sc bs rest -> do
        after <- live join rest
        ls <- mapM (\(_, _, b) -> live (Just (x, after)) b) bs
        _ <- def x after
        pure (atomSet sc <> mconcat ls)
      Dup v rest -> S.insert v <$> live join rest
      Drop v rest -> S.insert v <$> live join rest
      DropReuse v _ t rest -> live join rest >>= def t . S.insert v >>= pure . S.insert v
    atomSet a = S.fromList [v | AVar v <- [a]]
    rhsUses rhs = drop 1 (uses (Bind "" rhs (Ret (AInt 0))))

data Loc = InReg String | InSlot Int
  deriving (Eq)

-- | A function's frame: where each variable lives and which registers to restore.
-- fLoop: the function's own label, when a call to itself in tail position can jump back to
-- where the arguments are stored instead of leaving and re-entering the frame.
-- fUses: how often each variable occurs (a comparison used once, by an if, becomes a branch).
data Slots = Slots {fLocs :: M.Map String Loc, fSaved :: [(String, Int)], fLoop :: Maybe String, fUses :: M.Map String Int, fParams :: [String], fFullReuse :: S.Set String}

-- | Tokens whose case branch proves that all pointer fields are taken over. Facts are
-- local to a branch, and die when the parent is consumed. No uniqueness is assumed here:
-- the emitter still checks its count, including the immortal bit, at the point of reuse.
fullFieldReuse :: M.Map (Integer, Int, Integer) Integer -> Expr -> S.Set String
fullFieldReuse layouts = go M.empty
  where
    maps = M.fromList [(lid, pointers) | ((_, _, pointers), lid) <- M.toList layouts]
    go known e = case e of
      Bind _ _ rest -> go known rest
      BindIf _ _ a b rest -> go known a <> go known b <> go known rest
      BindCase _ s bs rest ->
        S.unions [go (inBranch known s tag) b | (tag, _, b) <- bs] <> go known rest
      Dup _ rest -> go known rest
      Drop v rest -> go (M.delete v known) rest
      DropReuse v mask tok rest ->
        (if M.lookup v known == Just mask then S.singleton tok else S.empty) <> go (M.delete v known) rest
      Ret _ -> S.empty
    inBranch known (AVar v) tag = case M.lookup tag maps of
      Just pointers -> M.insert v pointers known
      Nothing -> M.delete v known
    inBranch known _ _ = known

emitFun :: Bool -> String -> Fun -> G ()
emitFun reuse lbl f@(Fun name params base env envPtrs dropsSelf body) = do
  when (length params > 7) $ error "more than 7 parameters"
  layouts <- gets gsLayouts
  let (locs, saved, frame) = allocate ["x" ++ show r | r <- [19 .. 28 :: Int]] f (params ++ env ++ bound body)
      slots = Slots locs saved (if null env && not dropsSelf then Just lbl else Nothing) (M.fromListWith (+) [(v, 1) | v <- uses body]) params (if reuse then fullFieldReuse layouts body else S.empty)
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
  saveRegs ("str", "stp") saved
  forM_ (zip [base ..] env) $ \(j, v) -> do
    ins ("ldr x9, [x0, #" ++ show (8 * j) ++ "]")
    store slots "x9" v
  forM_ (zip [1 :: Int ..] params) $ \(r, p) -> store slots ("x" ++ show r) p
  forM_ (fLoop slots >> reduction lbl f) (vectorLoop slots)
  line ("L" ++ lbl ++ "_loop:")
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
  saveRegs ("ldr", "ldp") (fSaved slots)
  epilogue

-- | An array's payload words for @n@ elements (2 + n elements, rounded up to words) into @d@,
-- after a compare whose ne means words (eq: 4-byte elements). Uses x16.
elemWords :: String -> String -> G ()
elemWords d n = do
  ins "cset x16, ne"
  ins "add x16, x16, #2" -- log2 of the element size
  ins ("lsl " ++ d ++ ", " ++ n ++ ", x16")
  ins ("add " ++ d ++ ", " ++ d ++ ", #23") -- + 7 to round up, + 16 for length and capacity
  ins ("lsr " ++ d ++ ", " ++ d ++ ", #3")

-- | Store or load callee-saved registers at their save offsets, two at a time where adjacent.
saveRegs :: (String, String) -> [(String, Int)] -> G ()
saveRegs (one, two) rs = case rs of
  (r1, o1) : (r2, o2) : more | o2 == o1 + 8, o1 <= 504 -> do
    ins (two ++ " " ++ r1 ++ ", " ++ r2 ++ ", [sp, #" ++ show o1 ++ "]")
    saveRegs (one, two) more
  (r, o) : more -> ins (one ++ " " ++ r ++ ", [sp, #" ++ show o ++ "]") >> saveRegs (one, two) more
  [] -> pure ()

-- | Every occurrence of a variable in a body (for ranking variables by use).
uses :: Expr -> [String]
uses e = case e of
  Ret a -> av a
  Bind x rhs rest -> x : rhsVars rhs ++ uses rest
  BindIf x c a b rest -> x : av c ++ uses a ++ uses b ++ uses rest
  BindCase x s bs rest -> x : av s ++ concat [uses b | (_, _, b) <- bs] ++ uses rest
  Dup v rest -> v : uses rest
  Drop v rest -> v : uses rest
  DropReuse v _ t rest -> v : t : uses rest
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
      RAlloc _ h as -> concatMap av (maybe [] pure h ++ as)
      RAllocAt t _ h as -> t : concatMap av (maybe [] pure h ++ as)
      RField a _ -> av a
      RHeader a _ -> av a
      RPushHandler cs _ -> concatMap (av . snd) cs
      RPopHandler a -> av a
      RPerform _ a -> av a
      RConv _ a -> av a
      RArray _ _ as -> concatMap av as
      RIndex a i _ -> av a ++ av i
      RArena _ -> []

-- | Variables bound in a body.
bound :: Expr -> [String]
bound e = case e of
  Ret _ -> []
  Bind x _ rest -> x : bound rest
  BindIf x _ a b rest -> x : bound a ++ bound b ++ bound rest
  BindCase x _ bs rest -> x : concat [bound b | (_, _, b) <- bs] ++ bound rest
  Dup _ rest -> bound rest
  Drop _ rest -> bound rest
  DropReuse _ _ tok rest -> tok : bound rest

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
  ANullary t -> modify (\s -> s {gsNullary = S.insert t (gsNullary s)}) >> address r ("_kn_" ++ show t)

-- | The register holding an atom: its own, if it lives in one; otherwise it is loaded into @r@.
operand :: Slots -> String -> Atom -> G String
operand slots r a = case a of
  AVar v | InReg x <- fLocs slots M.! v -> pure x
  AInt 0 -> pure "xzr"
  _ -> atom slots r a >> pure r

-- | The two operands of add, sub or cmp: the second may be a 12-bit immediate, and then the
-- first can't be xzr (that encoding means sp there).
operands :: Slots -> Atom -> Atom -> G (String, String)
operands slots a b = case b of
  AInt n | n >= 0, n < 4096 -> do
    ra <- operand slots "x9" a
    ra' <- if ra == "xzr" then ins "mov x9, #0" >> pure "x9" else pure ra
    pure (ra', "#" ++ show n)
  _ -> (,) <$> operand slots "x9" a <*> operand slots "x10" b

-- | Where a variable is computed: its own register, or x0 when it lives in a slot.
destOf :: Slots -> String -> String
destOf slots x = case fLocs slots M.! x of
  InReg r -> r
  InSlot _ -> "x0"

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
  ins "tst w17, #0x7ffffc00"
  ins "b.eq _keel_panic_rc"
  ins "add w17, w17, #1024"
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
  -- A comparison used only by the if after it: compare and branch, no 0/1 value.
  Bind c (RPrim op it a b) (BindIf x (AVar c') ea eb rest)
    | c == c', op `elem` [Eq, Lt], M.lookup c (fUses slots) == Just 2 -> do
        (ra, rb) <- operands slots a b
        ins ("cmp " ++ ra ++ ", " ++ rb)
        let otherwise' = if op == Eq then "ne" else if signed it then "ge" else "hs"
        ifThen x (\l -> ins ("b." ++ otherwise' ++ " " ++ l)) ea eb rest
  Bind x rhs rest -> do
    loc x
    let d = destOf slots x
    direct <- rhsInto slots d rhs
    unless direct (rhsCode slots rhs)
    when (not direct || d == "x0") $ store slots "x0" x
    expr slots join rest
  BindIf x c a b rest -> do
    rc <- operand slots "x9" c
    ifThen x (\l -> ins ("cbz " ++ rc ++ ", " ++ l)) a b rest
  BindCase x s bs rest -> do
    let tailPos = isNothingJ && returns x rest
    lJoin <- newLabel
    labels <- mapM (const newLabel) bs
    rs <- operand slots "x9" s
    ins ("ldr w9, [" ++ rs ++ ", #-8]")
    ins "and w9, w9, #0x3ff" -- the layout, in the header
    -- Compare against every layout but the last, whose branch comes first and falls through.
    forM_ (zip (init bs) labels) $ \((tag, _, _), l) -> do
      ins ("cmp x9, #" ++ show tag)
      ins ("b.eq " ++ l)
    forM_ (zip (last bs : init bs) (last labels : init labels)) $ \((_, _, body), l) -> do
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
  DropReuse v mask tok rest -> do
    load' slots "x0" v
    if tok `S.member` fFullReuse slots then do
      lSlow <- newLabel
      lDone <- newLabel
      ins "ldr w9, [x0, #-8]"
      ins "lsr w10, w9, #10" -- count plus immortal bit: exactly 1 is unique
      ins "cmp w10, #1"
      ins ("b.ne " ++ lSlow)
      -- Same freed counter and count-zero token as the helper. All child references move
      -- to the caller, so there is no child walk (also inside an arena).
      address "x12" "_keel_stats"
      ins "ldr x13, [x12, #24]"
      ins "add x13, x13, #1"
      ins "str x13, [x12, #24]"
      ins "and w9, w9, #0x3ff"
      ins "str w9, [x0, #-8]" -- leave the narrow field in the upper half untouched
      ins ("b " ++ lDone)
      line (lSlow ++ ":")
      genericReuse
      line (lDone ++ ":")
    else genericReuse
    store slots "x0" tok
    expr slots join rest
    where
      genericReuse = movImm "x1" mask >> ins "bl _keel_drop_reuse"
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

    -- A call in tail position: load the arguments, drop the frame, jump.
    tailCall rhs = case rhs of
      RCall f a -> Just $ do
        atom slots "x0" f
        atom slots "x1" a
        ins "ldr x16, [x0]"
        leave slots
        ins "br x16"
      RCallKnown i as
        | fLoop slots == Just ("_kf_" ++ show i) -> Just $ do
            moves slots [(fLocs slots M.! p, a) | (p, a) <- zip (fParams slots) as]
            ins ("b L_kf_" ++ show i ++ "_loop")
        | otherwise -> Just $ do
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

-- | A reduction over an array, the shape of @scan@ in bench/goose/sum.kl:
--
-- > f … xs … i … acc … = if i == length xs then acc else f … xs … (i + 1) … (acc + e) …
--
-- where e is computed from @get xs i@ (unchecked: "Keel.Range" proved the index in bounds), the
-- parameters passed on unchanged, and constants, by 64-bit @land lor lxor +% -%@ and
-- conversions to 64 bits (an @i32@ element's @as i64@).
data Reduction = Reduction
  { rXs, rI, rAcc, rE :: String
  , rChecked :: Bool                  -- ^ acc + e panics on overflow (else it wraps)
  , rNodes :: [(String, Prim, Atom, Atom)] -- ^ e's computation, in order
  , rElems :: [String]                -- ^ variables holding get xs i (or it converted)
  , rElem :: Elem                     -- ^ how xs holds its elements
  }

reduction :: String -> Fun -> Maybe Reduction
reduction lbl (Fun _ params _ [] _ False body) = case body of
  Bind l (RArray ALength _ [AVar xs]) (Bind c (RPrim Eq _ x y) (BindIf r (AVar c') _ els (Ret (AVar r'))))
    | c == c', r == r', Just i <- counter -> do
        (binds, args) <- straight els
        i1 <- listToMaybe [t | (t, RPrim (Arith ov Add) it (AVar i') (AInt 1)) <- binds, i' == i, ov /= Saturate, ov /= Optional, bits it == 64]
        -- acc: the parameter added to (the branch that ends the loop doesn't matter here)
        (acc, acc1, checked, e) <- listToMaybe [(a, t, ov == Checked, e) | (t, RPrim (Arith ov Add) it (AVar a) (AVar e)) <- binds, a `elem` params, ov `elem` [Checked, Wrap], bits it == 64, ov == Wrap || signed it]
        let loads = [(t, k) | (t, RIndex (AVar xs') (AVar i') k) <- binds, xs' == xs, i' == i]
            -- A conversion to 64 bits doesn't change a canonical value: another name for it.
            convs = [(t, v) | (t, RConv to (AVar v)) <- binds, bits to == 64]
            name v = maybe v name (lookup v convs)
            nm a = case a of
              AVar v -> AVar (name v)
              _ -> a
            elems = map fst loads
            nodes = [(t, op, nm a, nm b) | (t, RPrim op it a b) <- binds, t `notElem` [i1, acc1], bits it == 64, op `elem` vectorOps]
            invariant = [p | (p, AVar a) <- zip params args, a == p]
            known v = v `elem` elems || v `elem` invariant || v `elem` [t | (t, _, _, _) <- nodes]
            operandOk a = case a of
              AVar v -> v `notElem` [i, acc] && known v
              AInt _ -> True
              _ -> False
        k <- listToMaybe (map snd loads)
        if args == [if p == i then AVar i1 else if p == acc then AVar acc1 else AVar p | p <- params]
          && xs `elem` invariant
          && all ((== k) . snd) loads
          && length binds == 2 + length elems + length nodes + length convs
          && all (\(_, _, a, b) -> operandOk a && operandOk b) nodes
          && known (name e)
          then Just (Reduction xs i acc (name e) checked nodes elems k)
          else Nothing
    where
      counter = case (x, y) of
        (AVar v, AVar w) | w == l -> Just v
        (AVar v, AVar w) | v == l -> Just w
        _ -> Nothing
  _ -> Nothing
  where
    -- The else branch: plain bindings, then the call to this function in tail position.
    straight e = case e of
      Bind t (RCallKnown j as) (Ret (AVar t')) | t == t', "_kf_" ++ show j == lbl -> Just ([], as)
      Bind t rhs rest -> (\(bs, as) -> ((t, rhs) : bs, as)) <$> straight rest
      _ -> Nothing
reduction _ _ = Nothing

vectorOps :: [Prim]
vectorOps = [Bits And, Bits Or, Bits Xor, Arith Wrap Add, Arith Wrap Sub]

-- | The reduction several elements at a time, from the current i to the last multiple of a
-- step before the end; the scalar loop does the rest. Each iteration loads two NEON registers:
-- four 8-byte elements, or eight 4-byte ones widened to 64 bits (four registers of two lanes).
-- With a checked acc + e, the result is kept only if every e was ≥ 0 and no lane's sum
-- overflowed: then the running sum only grows, so adding the lanes to acc with checked adds
-- panics exactly when some step of the scalar loop would. Otherwise nothing was stored, and
-- the scalar loop starts over from the same i (the loop is pure, so running it again shows no
-- difference).
--
-- Registers, with u = 2 or 4 registers per value: v0… the lane sums, v4–v7 the invariants and
-- constants, v16… the elements, v20–v27 the other values, v30 and v31 the sign bits seen (two
-- chains, one OR each per iteration), v28 and v29 the ORs feeding them; v8–v15 are
-- callee-saved in C.
-- ponytail: one loop shape, recognised by pattern; a loop IR when more loops need it.
vectorLoop :: Slots -> Reduction -> G ()
vectorLoop slots red = when (length scalars <= 4 && u * length (rNodes red) <= 8) $ do
  lSkip <- newLabel
  lLoop <- newLabel
  atom slots "x9" (AVar (rXs red))
  atom slots "x10" (AVar (rI red))
  ins "ldr x11, [x9]"
  ins "sub x12, x11, x10"
  ins ("cmp x12, #" ++ show step)
  ins ("b.lt " ++ lSkip)
  ins ("and x12, x12, #-" ++ show step)
  ins "add x13, x9, #16"
  ins ("add x13, x13, x10, lsl #" ++ show sh)
  ins ("add x14, x13, x12, lsl #" ++ show sh)
  forM_ (map sum' halves ++ ["v30", "v31"]) $ \v -> ins ("movi " ++ v ++ ".2d, #0")
  forM_ (zip scalars [4 :: Int ..]) $ \(a, k) -> atom slots "x15" a >> ins ("dup v" ++ show k ++ ".2d, x15")
  line (lLoop ++ ":")
  ins "ldp q16, q17, [x13], #32"
  case rElem red of
    -- Widen in place, last first: v18, v19 from v17, then v16, v17 from v16.
    ENarrow sgn -> do
      let xtl = if sgn then "sxtl" else "uxtl"
      ins (xtl ++ "2 v19.2d, v17.4s")
      ins (xtl ++ " v18.2d, v17.2s")
      ins (xtl ++ "2 v17.2d, v16.4s")
      ins (xtl ++ " v16.2d, v16.2s")
    _ -> pure ()
  forM_ (rNodes red) $ \(t, op, a, b) -> forM_ halves $ \h ->
    ins (opName op ++ " " ++ vreg (AVar t) h ++ arr op ++ ", " ++ vreg a h ++ arr op ++ ", " ++ vreg b h ++ arr op)
  let e = AVar (rE red)
  forM_ halves $ \h -> ins ("add " ++ sum' h ++ ".2d, " ++ sum' h ++ ".2d, " ++ vreg e h ++ ".2d")
  when (rChecked red) $ do
    orAll "v28" [vreg e h | h <- halves]
    orAll "v29" (map sum' halves)
    ins "orr v30.16b, v30.16b, v28.16b"
    ins "orr v31.16b, v31.16b, v29.16b"
  ins "cmp x13, x14"
  ins ("b.ne " ++ lLoop)
  when (rChecked red) $ do
    ins "orr v30.16b, v30.16b, v31.16b"
    ins "mov x15, v30.d[0]"
    ins "mov x16, v30.d[1]"
    ins "orr x15, x15, x16"
    ins ("tbnz x15, #63, " ++ lSkip)
  atom slots "x15" (AVar (rAcc red))
  forM_ [sum' h ++ ".d[" ++ show lane ++ "]" | h <- halves, lane <- [0, 1 :: Int]] $ \l -> do
    ins ("mov x16, " ++ l)
    if rChecked red
      then ins "adds x15, x15, x16" >> ins "b.vs _keel_panic_overflow"
      else ins "add x15, x15, x16"
  ins "add x10, x10, x12"
  store slots "x10" (rI red)
  store slots "x15" (rAcc red)
  line (lSkip ++ ":")
  where
    (u, sh) = case rElem red of
      ENarrow _ -> (4, 2 :: Int)
      _ -> (2, 3)
    halves = [0 .. u - 1] :: [Int]
    step = 2 * u
    sum' h = "v" ++ show h
    temps = rElems red ++ [t | (t, _, _, _) <- rNodes red]
    scalars = nub [o | (_, _, a, b) <- rNodes red, o <- [a, b], case o of AVar v -> v `notElem` temps; _ -> True]
    vreg a h = case a of
      AVar v | v `elem` rElems red -> "v" ++ show (16 + h)
      AVar v | Just k <- elemIndex v [t | (t, _, _, _) <- rNodes red] -> "v" ++ show (20 + u * k + h)
      _ -> "v" ++ show (4 + fromMaybe 0 (elemIndex a scalars))
    orAll d (v : w : vs) = do
      ins ("orr " ++ d ++ ".16b, " ++ v ++ ".16b, " ++ w ++ ".16b")
      forM_ vs $ \x -> ins ("orr " ++ d ++ ".16b, " ++ d ++ ".16b, " ++ x ++ ".16b")
    orAll _ _ = pure ()
    opName op = case op of
      Bits And -> "and"
      Bits Or -> "orr"
      Bits Xor -> "eor"
      Arith _ Sub -> "sub"
      _ -> "add"
    arr op = case op of
      Bits _ -> ".16b"
      _ -> ".2d"

-- | Move atoms into locations all at once (a self tail call's arguments into its parameters):
-- a move waits while its destination is still to be read; a cycle goes through a scratch
-- register (x10–x15: at most three cycles among seven parameters).
moves :: Slots -> [(Loc, Atom)] -> G ()
moves slots ms0 = go [(d, src a) | (d, a) <- ms0, src a /= Left d] ["x10", "x11", "x12", "x13", "x14", "x15"]
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
      (InSlot i, Left (InReg r)) -> ins ("str " ++ r ++ ", [sp, #" ++ show (8 * i) ++ "]")
      (InSlot i, Left l) -> load "x9" l >> ins ("str x9, [sp, #" ++ show (8 * i) ++ "]")
      (InSlot i, Right a) -> atom slots "x9" a >> ins ("str x9, [sp, #" ++ show (8 * i) ++ "]")
    load r l = case l of
      InReg x -> unless (x == r) $ ins ("mov " ++ r ++ ", " ++ x)
      InSlot i -> ins ("ldr " ++ r ++ ", [sp, #" ++ show (8 * i) ++ "]")

-- | Allocate a block of @n@ payload words of a layout into x0 (header written).
-- The runtime allocator clobbers only x0, x1 and x13–x16.
alloc :: Int -> Integer -> G ()
alloc n lid = do
  t <- gets (\st -> template (gsLayouts st) lid)
  movImm "x0" (toInteger n)
  movImm "x1" t
  ins "bl _keel_alloc"

-- | The words (bits 0–7) and pointer map (8–23) of each layout whose header holds a field,
-- from fieldLayouts on: what the runtime needs to free such a block.
layoutTable :: M.Map (Integer, Int, Integer) Integer -> G ()
layoutTable layouts = do
  line "\t.p2align 2"
  line "_keel_layouts:"
  let byId = M.fromList [(i, (n, bm)) | ((_, n, bm), i) <- M.toList layouts]
  forM_ [fieldLayouts .. maybe (fieldLayouts - 1) fst (M.lookupMax byId)] $ \i ->
    ins (".word " ++ show (maybe 0 (\(n, bm) -> toInteger n .|. (bm `shiftL` 8)) (M.lookup i byId)))
  line "\t.p2align 3"

-- | Header word of a fresh block: count 1 and its layout.
-- The low half: the layout in bits 0–9, the count in bits 10–30 (so it moves by 1024), bit 31
-- immortal. A count that overflows carries into bit 31: the block becomes immortal (it leaks).
-- The high half is the block's field, for layouts from fieldLayouts on (the runtime finds their
-- words and pointer map in _keel_layouts); otherwise their words (bits 32–39) and pointer map
-- (40–55). A free block of no words keeps its free-list link there.
header :: M.Map (Integer, Int, Integer) Integer -> Integer -> Integer
header layouts lid = 1024 .|. template layouts lid

-- | A header without its count.
template :: M.Map (Integer, Int, Integer) Integer -> Integer -> Integer
template layouts lid = case [(n, bm) | ((_, n, bm), i) <- M.toList layouts, i == lid, lid < fieldLayouts] of
  (n, bm) : _ -> lid .|. (toInteger n `shiftL` 32) .|. (bm `shiftL` 40)
  [] -> lid

-- | The common right-hand sides, computed straight into register @d@ from their operands'
-- registers; False for the rest (rhsCode computes those into x0).
rhsInto :: Slots -> String -> Rhs -> G Bool
rhsInto slots d rhs = case rhs of
  RAtom a -> atom slots d a >> pure True
  RPrim Eq _ a b -> compare' a b "eq"
  RPrim Lt it a b -> compare' a b (if signed it then "lt" else "lo")
  RPrim (Arith ov aop) (IntTy sgn 64) a b
    | ov `elem` [Wrap, Checked], aop `elem` [Add, Sub] -> do
        (ra, rb) <- operands slots a b
        let op = (if aop == Add then "add" else "sub") ++ (if ov == Checked then "s" else "")
        ins (op ++ " " ++ d ++ ", " ++ ra ++ ", " ++ rb)
        when (ov == Checked) $
          ins ("b." ++ (if sgn then "vs" else if aop == Add then "cs" else "lo") ++ " _keel_panic_overflow")
        pure True
    | ov `elem` [Wrap, Checked], aop == Mul -> do
        ra <- operand slots "x9" a
        rb <- operand slots "x10" b
        when (ov == Checked) $ -- the high half first: d may share a register with an operand
          ins ((if sgn then "smulh" else "umulh") ++ " x11, " ++ ra ++ ", " ++ rb)
        ins ("mul " ++ d ++ ", " ++ ra ++ ", " ++ rb)
        when (ov == Checked) $
          if sgn
            then ins ("cmp x11, " ++ d ++ ", asr #63") >> ins "b.ne _keel_panic_overflow"
            else ins "cbnz x11, _keel_panic_overflow"
        pure True
  -- Canonical (sign- or zero-extended) operands give a canonical result: any width.
  RPrim (Bits bop) _ a b | bop `elem` [And, Or, Xor] -> do
    ra <- operand slots "x9" a
    rb <- operand slots "x10" b
    ins ((case bop of And -> "and"; Or -> "orr"; _ -> "eor") ++ " " ++ d ++ ", " ++ ra ++ ", " ++ rb)
    pure True
  RField a i -> do
    ra <- operand slots "x9" a
    ins ("ldr " ++ d ++ ", [" ++ ra ++ ", #" ++ show (8 * i) ++ "]")
    pure True
  RHeader a sgn -> do
    ra <- operand slots "x9" a
    ins (headerRead sgn d ++ ", [" ++ ra ++ ", #-4]")
    pure True
  -- To a 64-bit type the canonical form doesn't change: a move. Narrower: re-extend.
  RConv to a | bits to == 64 -> atom slots d a >> pure True
  RConv to@(IntTy sgn n) a -> do
    ra <- operand slots "x9" a
    let w r = 'w' : drop 1 r
    ins $ case () of
      _ | sgn -> (case n of 8 -> "sxtb "; 16 -> "sxth "; _ -> "sxtw ") ++ d ++ ", " ++ w ra
        | n == 32 -> "mov " ++ w d ++ ", " ++ w ra
        | otherwise -> "and " ++ d ++ ", " ++ ra ++ ", #" ++ show (snd (intRange to))
    pure True
  -- A shift by a constant in range: one instruction. A right shift of a canonical value stays
  -- canonical; a left shift only at 64 bits, where nothing needs re-extending.
  RPrim (Bits bop) (IntTy sgn n) a (AInt k)
    | k >= 0, k < 64, bop == Shr || (bop == Shl && n == 64) -> do
        ra <- operand slots "x9" a
        ins ((if bop == Shl then "lsl " else if sgn then "asr " else "lsr ") ++ d ++ ", " ++ ra ++ ", #" ++ show k)
        pure True
  -- Division by a constant that is neither 0 nor -1 can't panic.
  RPrim (Arith Checked aop) (IntTy sgn _) a (AInt k)
    | aop `elem` [Div, Rem], k /= 0, k /= -1 || not sgn -> do
        ra <- operand slots "x9" a
        movImm "x10" k
        ins ((if sgn then "sdiv" else "udiv") ++ " x11, " ++ ra ++ ", x10")
        ins (if aop == Div then "mov " ++ d ++ ", x11" else "msub " ++ d ++ ", x11, x10, " ++ ra)
        pure True
  RArray ALength _ [a] -> do
    ra <- operand slots "x9" a
    ins ("ldr " ++ d ++ ", [" ++ ra ++ "]")
    pure True
  RArray AGet e [a, i] -> do
    ra <- operand slots "x9" a
    ri <- operand slots "x10" i
    ins ("ldr x11, [" ++ ra ++ "]")
    ins ("cmp " ++ ri ++ ", x11")
    ins "b.hs _keel_panic_bounds" -- unsigned: a negative index is out of bounds too
    element e d ra ri
    pure True
  RIndex a i e -> do
    ra <- operand slots "x9" a
    ri <- operand slots "x10" i
    element e d ra ri
    pure True
  _ -> pure False
  where
    compare' a b cond = do
      (ra, rb) <- operands slots a b
      ins ("cmp " ++ ra ++ ", " ++ rb)
      ins ("cset " ++ d ++ ", " ++ cond)
      pure True

-- | Load element ri of array ra into d (uses x11).
element :: Elem -> String -> String -> String -> G ()
element e d ra ri = do
  ins ("add x11, " ++ ra ++ ", " ++ ri ++ ", lsl #" ++ (case e of ENarrow _ -> "2"; _ -> "3"))
  ins ((case e of ENarrow sgn -> headerRead sgn d; _ -> "ldr " ++ d) ++ ", [x11, #16]")

-- | Load the header field into register x…: sign- or zero-extended to the canonical form.
headerRead :: Bool -> String -> String
headerRead sgn d = if sgn then "ldrsw " ++ d else "ldr w" ++ drop 1 d

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
  RClosure i fvs lid -> do
    alloc (1 + length fvs) lid
    address "x11" ("_kf_" ++ show i)
    ins "str x11, [x0]"
    storeAll 1 fvs
  RCodata is fvs lid -> do
    alloc (length is + length fvs) lid
    forM_ (zip [0 :: Int ..] is) $ \(j, i) -> do
      address "x11" ("_kf_" ++ show i)
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
    storeAll (length is) fvs
  RProj a i -> do
    atom slots "x0" a
    ins "mov x1, #0"
    ins ("ldr x16, [x0, #" ++ show (8 * i) ++ "]")
    ins "blr x16"
  RAlloc lid h as -> do
    alloc (length as) lid
    fields h as
  RAllocAt tok lid h as -> do
    -- In place if the token holds a block (it was unique); otherwise allocate.
    lFresh <- newLabel
    lDone <- newLabel
    load' slots "x0" tok
    ins ("cbz x0, " ++ lFresh)
    gets (\st -> header (gsLayouts st) lid) >>= movImm "x15"
    ins "str x15, [x0, #-8]"
    address "x13" "_keel_stats"
    ins "ldr x14, [x13, #16]"
    ins "add x14, x14, #1"
    ins "str x14, [x13, #16]"
    ins ("b " ++ lDone)
    line (lFresh ++ ":")
    alloc (length as) lid
    line (lDone ++ ":")
    fields h as
  RField a i -> do
    atom slots "x9" a
    ins ("ldr x0, [x9, #" ++ show (8 * i) ++ "]")
  RHeader a sgn -> atom slots "x9" a >> ins (headerRead sgn "x0" ++ ", [x9, #-4]")
  RPushHandler cs lid -> do
    alloc (2 + 2 * length cs) lid
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
  RArena True -> ins "bl _keel_arena_open"
  RArena False -> ins "bl _keel_arena_close"
  -- Arrays (spec/memory.md): length and get read the block; the rest are runtime routines.
  RArray ALength _ [a] -> atom slots "x9" a >> ins "ldr x0, [x9]"
  RArray AGet e [a, i] -> do
    atom slots "x9" a
    atom slots "x10" i
    ins "ldr x11, [x9]"
    ins "cmp x10, x11"
    ins "b.hs _keel_panic_bounds" -- unsigned: a negative index is out of bounds too
    element e "x0" "x9" "x10"
  RIndex a i e -> atom slots "x9" a >> atom slots "x10" i >> element e "x0" "x9" "x10"
  RArray op e as -> do
    forM_ (zip [0 :: Int ..] as) $ \(r, a) -> atom slots ("x" ++ show r) a
    case op of
      AEmpty -> ins "mov x0, #0" >> ins ("mov x1, #" ++ kind) >> ins "bl _keel_array_alloc"
      ANew -> ins ("mov x2, #" ++ kind) >> ins "bl _keel_array_new"
      ASet -> ins "bl _keel_array_set"
      -- A unique array with room: store and count, without calling the runtime.
      APush -> do
        lSlow <- newLabel
        lDone <- newLabel
        ins "ldp x9, x10, [x0]"
        ins "cmp x9, x10"
        ins ("b.hs " ++ lSlow)
        ins "ldr w11, [x0, #-8]"
        ins "lsr w11, w11, #10"
        ins "cmp w11, #1"
        ins ("b.ne " ++ lSlow)
        case e of
          ENarrow _ -> ins "add x11, x0, x9, lsl #2" >> ins "str w1, [x11, #16]"
          _ -> ins "add x11, x0, x9, lsl #3" >> ins "str x1, [x11, #16]"
        ins "add x9, x9, #1"
        ins "str x9, [x0]"
        ins ("b " ++ lDone)
        line (lSlow ++ ":")
        ins "bl _keel_array_push"
        line (lDone ++ ":")
      _ -> ins "bl _keel_array_pop"
    where
      kind = show (elemKind e)
  where
    storeAll :: Int -> [String] -> G ()
    storeAll from vs = forM_ (zip [from ..] vs) $ \(j, v) -> do
      load' slots "x11" v
      ins ("str x11, [x0, #" ++ show (8 * j) ++ "]")
    fields :: Maybe Atom -> [Atom] -> G ()
    fields h as = do
      forM_ h $ \a -> atom slots "x11" a >> ins "str w11, [x0, #-4]"
      forM_ (zip [0 :: Int ..] as) $ \(j, a) -> do
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
          (none, some) <- gets (\st -> optionLayouts (gsLayouts st) it)
          ins "mov x12, x0" -- the allocator leaves x9–x12 alone
          if narrow
            then alloc 0 some >> ins "str w12, [x0, #-4]"
            else alloc 1 some >> ins "str x12, [x0]"
          ins ("b " ++ lDone)
          line (lOvf ++ ":")
          atom (Slots M.empty [] Nothing M.empty [] S.empty) "x0" (ANullary none)
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
      TData "Array" [a] -> [a]
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
      -- Constructors never built at this type have no layout, and no block to print.
      let built = [(c, fts, lid, h, ws) | (c, fs) <- cs, let fts = map inst fs, let (key, h, ws) = dataLayoutKey (conNumbers decls M.! c) fts, Just lid <- [M.lookup key layouts]]
      lDone <- newLabel
      labels <- mapM (const newLabel) built
      ins "ldr x9, [sp, #16]"
      ins "ldr w9, [x9, #-8]"
      ins "and w9, w9, #0x3ff"
      forM_ (zip built labels) $ \((_, _, lid, _, _), l) -> do
        movImm "x10" lid
        ins "cmp x9, x10"
        ins ("b.eq " ++ l)
      ins ("b " ++ lDone)
      forM_ (zip built labels) $ \((c, fts, _, h, ws), l) -> do
        line (l ++ ":")
        printStr c
        unless (null fts) $ do
          printStr "("
          forM_ (zip [0 :: Int ..] fts) $ \(i, ft) -> do
            when (i > 0) $ printStr ", "
            field (if h == Just i then Left (case ft of TInt it -> signed it; _ -> False) else Right (fromMaybe i (elemIndex i ws))) ft
          printStr ")"
        ins ("b " ++ lDone)
      line (lDone ++ ":")
    TData "Array" [a] -> do
      lLoop <- newLabel
      lFirst <- newLabel
      lDone <- newLabel
      printStr "["
      ins "str xzr, [sp, #24]" -- the index
      line (lLoop ++ ":")
      ins "ldp x9, x11, [sp, #16]"
      ins "ldr x10, [x9]"
      ins "cmp x11, x10"
      ins ("b.hs " ++ lDone)
      ins ("cbz x11, " ++ lFirst)
      printStr ", "
      line (lFirst ++ ":")
      ins "ldp x9, x11, [sp, #16]"
      element (elemOf a) "x0" "x9" "x11"
      maybe (printStr "...") (\(_, l) -> ins ("bl " ++ l)) (M.lookup (prettyTy a) printers)
      ins "ldr x11, [sp, #24]"
      ins "add x11, x11, #1"
      ins "str x11, [sp, #24]"
      ins ("b " ++ lLoop)
      line (lDone ++ ":")
      printStr "]"
    TData _ _ -> printStr "<codata>"
    _ -> printStr "<closure>"
  epilogue
  ins "ret"
  where
    -- Print word i of the block (-1: the value itself), or its header field (Left: whether
    -- signed), with its type's printer.
    field :: Either Bool Int -> Ty -> G ()
    field place ft = do
      ins "ldr x0, [sp, #16]"
      case place of
        Left sgn -> ins (headerRead sgn "x0" ++ ", [x0, #-4]")
        Right i -> when (i >= 0) $ ins ("ldr x0, [x0, #" ++ show (8 * i) ++ "]")
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
  -- _keel_alloc: x0 = payload words, x1 = header without its count → x0 = payload. Clobbers
  -- x13–x16 only.
  fn "_keel_alloc"
  ins ("cmp x0, #" ++ show maxSmall)
  ins "b.hi L_alloc_bump"
  -- The free lists, or an empty table while an arena is open: then everything comes from the
  -- bump pointer, so all of it lies above the arena's start and goes when it closes.
  ins "adrp x13, _keel_fl@PAGE"
  ins "ldr x13, [x13, _keel_fl@PAGEOFF]"
  ins "ldr x14, [x13, x0, lsl #3]"
  ins "cbz x14, L_alloc_bump"
  ins "cbz x0, L_alloc_link0"
  ins "ldr x15, [x14]" -- the next free block
  line "L_alloc_pop:"
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
  ins "orr x15, x1, #1024" -- count 1
  ins "str x15, [x14, #-8]"
  ins "mov x0, x14"
  ins "ret"
  -- A block of no words links to the next in its header's high half, in words from it.
  line "L_alloc_link0:"
  ins "ldrsw x15, [x14, #-4]"
  ins "add x16, x14, x15, lsl #3"
  ins "cmp x15, #0"
  ins "csel x15, xzr, x16, eq"
  ins "b L_alloc_pop"

  -- Arenas (spec/memory.md). Opening one takes a record [base before, enclosing record, bump
  -- allocations so far] from the bump pointer; while any is open, _keel_drop leaves blocks at
  -- or above _keel_arena_base (the outermost record) alone. Closing resets the bump pointer to
  -- the record: everything allocated since is freed at once, and counted as freed.
  fn "_keel_arena_open"
  address "x13" "_keel_heap_ptr"
  ins "ldr x14, [x13]"
  ins "add x15, x14, #24"
  ins "ldr x16, [x13, #8]"
  ins "cmp x15, x16"
  ins "b.hi _keel_panic_oom"
  ins "str x15, [x13]"
  address "x10" "_keel_arena_base"
  ins "ldr x11, [x10]"
  address "x12" "_keel_arena_top"
  ins "ldr x9, [x12]"
  ins "stp x11, x9, [x14]"
  address "x15" "_keel_stats"
  ins "ldr x15, [x15]"
  ins "str x15, [x14, #16]"
  ins "str x14, [x12]"
  ins "cmp x11, x14"
  ins "csel x11, x11, x14, lo"
  ins "str x11, [x10]"
  address "x10" "_keel_nofree"
  address "x11" "_keel_fl"
  ins "str x10, [x11]"
  ins "mov x0, #0"
  ins "ret"

  fn "_keel_arena_close"
  address "x12" "_keel_arena_top"
  ins "ldr x14, [x12]"
  ins "ldp x11, x9, [x14]"
  address "x10" "_keel_arena_base"
  ins "str x11, [x10]"
  ins "str x9, [x12]"
  address "x13" "_keel_stats"
  ins "ldr x15, [x13]"
  ins "ldr x16, [x14, #16]"
  ins "sub x15, x15, x16"
  ins "ldr x16, [x13, #24]"
  ins "add x16, x16, x15"
  ins "str x16, [x13, #24]"
  -- … and not again when the enclosing arena closes.
  ins "cbz x9, L_close_outermost"
  ins "ldr x16, [x9, #16]"
  ins "add x16, x16, x15"
  ins "str x16, [x9, #16]"
  line "L_close_outermost:"
  address "x13" "_keel_heap_ptr"
  ins "str x14, [x13]"
  ins "cmn x11, #1" -- the outermost arena closed: the free lists are back
  ins "b.ne L_close_ret"
  address "x10" "_keel_freelists"
  address "x11" "_keel_fl"
  ins "str x10, [x11]"
  line "L_close_ret:"
  ins "mov x0, #0"
  ins "ret"

  -- _keel_drop: x0 = block. Decrement; at zero, drop the children and free the block. The last
  -- pointer child is handled by looping, so dropping a long list uses constant stack.
  fn "_keel_drop"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  line "L_drop_top:"
  ins "ldr w9, [x0, #-8]"
  ins "tbnz w9, #31, L_drop_ret"
  ins "tst w9, #0x7ffffc00"
  ins "b.eq _keel_panic_rc"
  ins "sub w9, w9, #1024"
  ins "str w9, [x0, #-8]"
  ins "tst w9, #0x7ffffc00"
  ins "b.ne L_drop_ret"
  address "x12" "_keel_arena_base"
  ins "ldr x12, [x12]"
  ins "cmp x0, x12"
  ins "b.hs L_drop_ret" -- in an open arena: freed when it closes
  stat 24 "x12" "x13"
  ins "str x0, [sp, #16]"
  ins "and w12, w9, #0x3ff"
  ins ("cmp w12, #" ++ show arrayLayout)
  ins "b.hs L_drop_special"
  ins "ldr x11, [x0, #-8]"
  ins "ubfx x11, x11, #40, #16" -- the pointer map
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
  -- A block with a field in its header: its pointer map is in the table.
  line "L_drop_special:"
  ins ("cmp w12, #" ++ show fieldLayouts)
  ins "b.lo L_drop_array"
  address "x11" "_keel_layouts"
  ins ("sub w12, w12, #" ++ show fieldLayouts)
  ins "ldr w11, [x11, x12, lsl #2]"
  ins "lsr w11, w11, #8"
  ins "b L_drop_loop"
  -- An array: drop its elements if they are pointers, last first, then free it.
  line "L_drop_array:"
  ins ("cmp w12, #" ++ show (arrayLayout + 2))
  ins "b.ne L_drop_free"
  ins "ldr x12, [x0]"
  line "L_drop_elems:"
  ins "cbz x12, L_drop_free"
  ins "sub x12, x12, #1"
  ins "str x12, [sp, #24]"
  ins "ldr x9, [sp, #16]"
  ins "add x9, x9, x12, lsl #3"
  ins "ldr x0, [x9, #16]"
  ins "bl _keel_drop"
  ins "ldr x12, [sp, #24]"
  ins "b L_drop_elems"

  -- _keel_free_block: x0 = block with count 0 → push it on its size's free list.
  fn "_keel_free_block"
  ins "ldr x10, [x0, #-8]"
  ins "ubfx x11, x10, #32, #8" -- its words (an array's: capped at 255)
  ins "tbz w10, #9, L_free_size" -- fieldLayouts = 512: the header holds a field
  ins "and w10, w10, #0x1ff"
  address "x11" "_keel_layouts"
  ins "ldr w11, [x11, x10, lsl #2]"
  ins "and w11, w11, #0xff"
  line "L_free_size:"
  ins ("cmp x11, #" ++ show maxSmall)
  ins "b.hi L_free_ret" -- ponytail: large blocks are not recycled
  address "x12" "_keel_freelists"
  ins "ldr x13, [x12, x11, lsl #3]"
  ins "cbz x11, L_free_link0"
  ins "str x13, [x0]" -- the link, in the first word
  ins "str x0, [x12, x11, lsl #3]"
  line "L_free_ret:"
  ins "ret"
  -- A block of no words: the link in its header's high half, in words from it (0: none).
  line "L_free_link0:"
  ins "sub x14, x13, x0"
  ins "asr x14, x14, #3"
  ins "cmp x13, #0"
  ins "csel x14, xzr, x14, eq"
  ins "str w14, [x0, #-4]"
  ins "str x0, [x12, x11, lsl #3]"
  ins "ret"

  -- _keel_drop_reuse: x0 = block, x1 = the fields taken over (a mask of words) → x0 = the
  -- block, if it was unique (its other children dropped, count 0 until reused), or 0 after an
  -- ordinary decrement and duplicating the fields taken over.
  fn "_keel_drop_reuse"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  ins "ldr w9, [x0, #-8]"
  ins "tbnz w9, #31, L_reuse_none"
  ins "tst w9, #0x7ffffc00"
  ins "b.eq _keel_panic_rc"
  ins "lsr w10, w9, #10"
  ins "cmp w10, #1"
  ins "b.ne L_reuse_shared"
  stat 24 "x12" "x13"
  ins "str x0, [sp, #16]"
  ins "ldr x11, [x0, #-8]"
  ins "ubfx x11, x11, #40, #16" -- the pointer map
  ins "tbz w9, #9, L_reuse_map"
  ins "and w12, w9, #0x1ff" -- a field in the header: the map is in the table
  address "x11" "_keel_layouts"
  ins "ldr w11, [x11, x12, lsl #2]"
  ins "lsr w11, w11, #8"
  line "L_reuse_map:"
  ins "bic x11, x11, x1" -- the fields taken over stay alive: they are the caller's now
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
  ins "ldr w9, [x0, #-8]"
  ins "and w9, w9, #0x3ff" -- count 0 until reused
  ins "str w9, [x0, #-8]"
  ins "b L_reuse_ret"
  line "L_reuse_shared:"
  ins "sub w9, w9, #1024"
  ins "str w9, [x0, #-8]"
  -- The block keeps its references: duplicate the fields taken over.
  line "L_reuse_none:"
  ins "cbz x1, L_reuse_zero"
  ins "rbit x13, x1"
  ins "clz x13, x13"
  ins "mov x14, #1"
  ins "lsl x14, x14, x13"
  ins "bic x1, x1, x14"
  ins "ldr x15, [x0, x13, lsl #3]"
  ins "ldr w16, [x15, #-8]"
  ins "tbnz w16, #31, L_reuse_none"
  ins "add w16, w16, #1024"
  ins "str w16, [x15, #-8]"
  ins "b L_reuse_none"
  line "L_reuse_zero:"
  ins "mov x0, #0"
  line "L_reuse_ret:"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  -- Arrays: payload [length, capacity, elements…]. The header's tag is 255 (an array) and its
  -- pointer map has bit 1 set if the elements are pointers; its size field is capacity + 2, at
  -- most 0xFF (larger blocks are never recycled anyway).
  -- An update to an array nothing else references happens in place; otherwise the array is
  -- copied first.

  -- An array's kind (spec/memory.md) is its layout minus arrayLayout: 0 for 4-byte elements,
  -- 1 for words, 2 for pointers. Its payload words: 2 + its capacity's elements, rounded up.

  -- _keel_array_alloc: x0 = capacity, x1 = kind → x0 = an empty array.
  fn "_keel_array_alloc"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  ins "stp x0, x1, [sp, #16]"
  ins "cmp x1, #0"
  elemWords "x0" "x0"
  ins "mov x11, x0" -- the allocator leaves x9–x12 alone
  ins "mov x1, #0"
  ins "bl _keel_alloc"
  ins "ldp x9, x10, [sp, #16]"
  movImm "x12" (1024 + arrayLayout) -- count 1, the kind's layout
  ins "add x12, x12, x10"
  ins "mov x13, #0xFF" -- its words, capped at 255
  ins "cmp x11, x13"
  ins "csel x11, x11, x13, lo"
  ins "orr x12, x12, x11, lsl #32"
  ins "str x12, [x0, #-8]"
  ins "stp xzr, x9, [x0]"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  -- _keel_array_new: x0 = length, x1 = the element (owned), x2 = kind → x0.
  fn "_keel_array_new"
  ins "stp x29, x30, [sp, #-48]!"
  ins "mov x29, sp"
  ins "tbnz x0, #63, _keel_panic_bounds"
  ins "stp x1, x2, [sp, #16]"
  ins "str x0, [sp, #32]"
  ins "mov x1, x2"
  ins "bl _keel_array_alloc"
  ins "ldr x9, [sp, #32]"
  ins "ldp x10, x11, [sp, #16]"
  ins "str x9, [x0]"
  ins "mov x12, #0"
  ins "cbz x11, L_anew_fill4"
  line "L_anew_fill:"
  ins "cmp x12, x9"
  ins "b.hs L_anew_filled"
  ins "add x13, x0, x12, lsl #3"
  ins "str x10, [x13, #16]"
  ins "add x12, x12, #1"
  ins "b L_anew_fill"
  line "L_anew_fill4:"
  ins "cmp x12, x9"
  ins "b.hs L_anew_filled"
  ins "add x13, x0, x12, lsl #2"
  ins "str w10, [x13, #16]"
  ins "add x12, x12, #1"
  ins "b L_anew_fill4"
  line "L_anew_filled:"
  ins "cmp x11, #2"
  ins "b.ne L_anew_ret"
  -- The element now has n references in the array; the caller gave one.
  ins "cbz x9, L_anew_drop"
  ins "ldr w13, [x10, #-8]"
  ins "tbnz w13, #31, L_anew_ret"
  ins "ubfx x14, x13, #10, #21"
  ins "add x14, x14, x9"
  ins "sub x14, x14, #1"
  ins "bfi w13, w14, #10, #21"
  ins "lsr x14, x14, #21" -- the count overflowed: immortal
  ins "cbz x14, L_anew_store"
  ins "orr w13, w13, #0x80000000"
  line "L_anew_store:"
  ins "str w13, [x10, #-8]"
  ins "b L_anew_ret"
  line "L_anew_drop:"
  ins "str x0, [sp, #32]"
  ins "mov x0, x10"
  ins "bl _keel_drop"
  ins "ldr x0, [sp, #32]"
  line "L_anew_ret:"
  ins "ldp x29, x30, [sp], #48"
  ins "ret"

  -- _keel_array_clone: x0 = array (owned), x1 = capacity ≥ its length → x0 = a fresh array with
  -- the same elements. A unique array's elements move and its block is freed; a shared one's
  -- are duplicated and its count decremented.
  fn "_keel_array_clone"
  ins "stp x29, x30, [sp, #-48]!"
  ins "mov x29, sp"
  ins "str x0, [sp, #16]"
  ins "ldr w9, [x0, #-8]"
  ins "mov x0, x1"
  ins "and w1, w9, #0x3ff"
  ins ("sub w1, w1, #" ++ show arrayLayout) -- the kind
  ins "bl _keel_array_alloc"
  ins "ldr x9, [sp, #16]"
  ins "ldr x10, [x9]"
  ins "str x10, [x0]"
  -- Copy the elements' words.
  ins "ldr w15, [x9, #-8]"
  ins "and w15, w15, #0x3ff"
  ins ("cmp w15, #" ++ show arrayLayout)
  elemWords "x15" "x10"
  ins "sub x15, x15, #2"
  ins "mov x11, #0"
  line "L_aclone_copy:"
  ins "cmp x11, x15"
  ins "b.hs L_aclone_copied"
  ins "add x12, x9, x11, lsl #3"
  ins "ldr x13, [x12, #16]"
  ins "add x12, x0, x11, lsl #3"
  ins "str x13, [x12, #16]"
  ins "add x11, x11, #1"
  ins "b L_aclone_copy"
  line "L_aclone_copied:"
  ins "ldr w12, [x9, #-8]"
  ins "lsr w13, w12, #10"
  ins "cmp w13, #1"
  ins "b.ne L_aclone_shared"
  ins "and w13, w12, #0x3ff" -- count 0
  ins "str w13, [x9, #-8]"
  address "x12" "_keel_arena_base"
  ins "ldr x12, [x12]"
  ins "cmp x9, x12"
  ins "b.hs L_aclone_ret" -- in an open arena: freed when it closes
  stat 24 "x12" "x13"
  ins "str x0, [sp, #32]"
  ins "mov x0, x9"
  ins "bl _keel_free_block"
  ins "ldr x0, [sp, #32]"
  ins "b L_aclone_ret"
  line "L_aclone_shared:"
  ins "and w13, w12, #0x3ff"
  ins ("cmp w13, #" ++ show (arrayLayout + 2))
  ins "b.ne L_aclone_dec"
  ins "mov x11, #0"
  line "L_aclone_dup:"
  ins "cmp x11, x10"
  ins "b.hs L_aclone_dec"
  ins "add x14, x9, x11, lsl #3"
  ins "ldr x14, [x14, #16]"
  ins "ldr w15, [x14, #-8]"
  ins "tbnz w15, #31, L_aclone_next"
  ins "add w15, w15, #1024"
  ins "str w15, [x14, #-8]"
  line "L_aclone_next:"
  ins "add x11, x11, #1"
  ins "b L_aclone_dup"
  line "L_aclone_dec:"
  ins "sub w12, w12, #1024"
  ins "str w12, [x9, #-8]"
  line "L_aclone_ret:"
  ins "ldp x29, x30, [sp], #48"
  ins "ret"

  -- _keel_array_set: x0 = array (owned), x1 = index, x2 = element (owned) → x0.
  fn "_keel_array_set"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  ins "ldr x9, [x0]"
  ins "cmp x1, x9"
  ins "b.hs _keel_panic_bounds"
  ins "ldr w10, [x0, #-8]"
  ins "lsr w10, w10, #10"
  ins "cmp w10, #1"
  ins "b.eq L_aset_store"
  ins "stp x1, x2, [sp, #16]"
  ins "ldr x1, [x0, #8]"
  ins "bl _keel_array_clone"
  ins "ldp x1, x2, [sp, #16]"
  line "L_aset_store:"
  ins "ldr w11, [x0, #-8]"
  ins "and w11, w11, #0x3ff"
  ins ("cmp w11, #" ++ show arrayLayout)
  ins "b.ne L_aset_word"
  ins "add x9, x0, x1, lsl #2"
  ins "str w2, [x9, #16]"
  ins "b L_aset_ret"
  line "L_aset_word:"
  ins "add x9, x0, x1, lsl #3"
  ins "ldr x10, [x9, #16]"
  ins "str x2, [x9, #16]"
  ins ("cmp w11, #" ++ show (arrayLayout + 2))
  ins "b.ne L_aset_ret"
  ins "str x0, [sp, #16]"
  ins "mov x0, x10"
  ins "bl _keel_drop" -- the element it replaced
  ins "ldr x0, [sp, #16]"
  line "L_aset_ret:"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  -- _keel_array_push: x0 = array (owned), x1 = element (owned) → x0. A full array doubles: in
  -- place when it is unique and the last block before the bump pointer (then nothing lies
  -- after it, not even an arena's record), otherwise into a copy.
  fn "_keel_array_push"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  ins "str x1, [sp, #16]"
  ins "ldp x9, x10, [x0]"
  ins "cmp x9, x10"
  ins "b.hs L_apush_grow"
  ins "ldr w11, [x0, #-8]"
  ins "lsr w11, w11, #10"
  ins "cmp w11, #1"
  ins "b.eq L_apush_store"
  ins "mov x1, x10"
  ins "bl _keel_array_clone"
  ins "b L_apush_store"
  line "L_apush_grow:"
  ins "lsl x1, x10, #1"
  ins "mov x12, #4"
  ins "cmp x1, x12"
  ins "csel x1, x1, x12, hs"
  ins "ldr w11, [x0, #-8]"
  ins "lsr w11, w11, #10"
  ins "cmp w11, #1"
  ins "b.ne L_apush_copy"
  ins "ldr w15, [x0, #-8]"
  ins "and w15, w15, #0x3ff"
  ins ("cmp w15, #" ++ show arrayLayout)
  elemWords "x12" "x10"
  ins "add x12, x0, x12, lsl #3" -- the block's end
  address "x13" "_keel_heap_ptr"
  ins "ldr x14, [x13]"
  ins "cmp x12, x14"
  ins "b.ne L_apush_copy"
  ins ("cmp w15, #" ++ show arrayLayout)
  elemWords "x15" "x1"
  ins "add x12, x0, x15, lsl #3"
  ins "ldr x14, [x13, #8]"
  ins "cmp x12, x14"
  ins "b.hi _keel_panic_oom"
  ins "str x12, [x13]"
  ins "str x1, [x0, #8]"
  -- The header's words (capped at 255, as in _keel_array_alloc).
  ins "mov x12, x15"
  ins "mov x13, #0xFF"
  ins "cmp x12, x13"
  ins "csel x12, x12, x13, lo"
  ins "ldr x13, [x0, #-8]"
  ins "bfi x13, x12, #32, #8"
  ins "str x13, [x0, #-8]"
  ins "b L_apush_store"
  line "L_apush_copy:"
  ins "bl _keel_array_clone"
  line "L_apush_store:"
  ins "ldr x9, [x0]"
  ins "ldr x1, [sp, #16]"
  ins "ldr w11, [x0, #-8]"
  ins "and w11, w11, #0x3ff"
  ins ("cmp w11, #" ++ show arrayLayout)
  ins "b.ne L_apush_word"
  ins "add x10, x0, x9, lsl #2"
  ins "str w1, [x10, #16]"
  ins "b L_apush_count"
  line "L_apush_word:"
  ins "add x10, x0, x9, lsl #3"
  ins "str x1, [x10, #16]"
  line "L_apush_count:"
  ins "add x9, x9, #1"
  ins "str x9, [x0]"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  -- _keel_array_pop: x0 = array (owned) → x0 without its last element.
  fn "_keel_array_pop"
  ins "stp x29, x30, [sp, #-32]!"
  ins "mov x29, sp"
  ins "ldr x9, [x0]"
  ins "cbz x9, _keel_panic_bounds"
  ins "ldr w11, [x0, #-8]"
  ins "lsr w11, w11, #10"
  ins "cmp w11, #1"
  ins "b.eq L_apop_take"
  ins "ldr x1, [x0, #8]"
  ins "bl _keel_array_clone"
  line "L_apop_take:"
  ins "ldr x9, [x0]"
  ins "sub x9, x9, #1"
  ins "str x9, [x0]"
  ins "ldr w11, [x0, #-8]"
  ins "and w11, w11, #0x3ff"
  ins ("cmp w11, #" ++ show (arrayLayout + 2))
  ins "b.ne L_apop_ret"
  ins "add x10, x0, x9, lsl #3"
  ins "str x0, [sp, #16]"
  ins "ldr x0, [x10, #16]"
  ins "bl _keel_drop"
  ins "ldr x0, [sp, #16]"
  line "L_apop_ret:"
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
  ins "add w15, w15, #1024"
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
  ins "cmp x0, #2" -- getc
  ins "b.eq L_perform_getc"
  ins "cmp x0, #7" -- openFile
  ins "b.eq L_perform_open"
  ins "cmp x0, #8" -- readByte
  ins "b.eq L_perform_read"
  ins "cmp x0, #9" -- closeFile
  ins "b.eq L_perform_close"
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
  line "L_perform_getc:"
  ins "bl _getchar" -- a byte, or EOF (-1)
  ins "sxtw x0, w0"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"
  -- openFile: x1 = the path, an Array u8 (owned). Copy it to the stack with a NUL, fopen it,
  -- and drop the array. The handle is the FILE pointer, or -1.
  line "L_perform_open:"
  ins "str x1, [x29, #16]"
  ins "ldr x9, [x1]"
  ins "add x10, x9, #16"
  ins "and x10, x10, #-16"
  ins "sub sp, sp, x10"
  ins "mov x11, #0"
  line "L_open_copy:"
  ins "cmp x11, x9"
  ins "b.hs L_open_copied"
  ins "add x12, x1, x11, lsl #2" -- 4-byte elements
  ins "ldr w12, [x12, #16]"
  ins "strb w12, [sp, x11]"
  ins "add x11, x11, #1"
  ins "b L_open_copy"
  line "L_open_copied:"
  ins "strb wzr, [sp, x9]"
  ins "mov x0, sp"
  mode <- str "rb"
  address "x1" mode
  ins "bl _fopen"
  ins "mov sp, x29"
  ins "cmp x0, #0"
  ins "csinv x0, x0, xzr, ne" -- NULL becomes -1
  ins "str x0, [x29, #24]"
  ins "ldr x0, [x29, #16]"
  ins "bl _keel_drop"
  ins "ldr x0, [x29, #24]"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"
  line "L_perform_read:"
  ins "mov x0, x1"
  ins "bl _fgetc" -- a byte, or EOF (-1)
  ins "sxtw x0, w0"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"
  line "L_perform_close:"
  ins "mov x0, x1"
  ins "bl _fclose"
  ins "mov x0, #0"
  ins "ldp x29, x30, [sp], #32"
  ins "ret"

  panic "_keel_panic_unhandled" "panic: unhandled operation (MMIO needs a freestanding target)\n"
  panic "_keel_panic_div" "panic: division by zero\n"
  panic "_keel_panic_bounds" "panic: array index out of bounds\n"
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
