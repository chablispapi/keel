-- | A portable assembler for the runtime (spec/backends.md): a record of instruction emitters
-- that each back end fills in, so "Keel.Runtime" writes a routine once for all three. The
-- output is still each back end's assembly text, through its own @G@ monad.
--
-- Registers: @A n@ the runtime's arguments and result (x0–x2, rax/rdi/rsi, a0–a2), @T n@
-- scratch, never overlapping an @A@. @T 0..3@ are all that @_keel_alloc@ and
-- @_keel_free_block@ may clobber; the code generators rely on that.
--
-- An emitter never uses a register it isn't given: where RISC-V needs one more (a bit test, a
-- lowest set bit, an indexed store, a statistics counter) the operation takes it as an
-- argument, and the other targets ignore it. An immediate the target can't encode is left to
-- the assembler to reject; the shared code moves large constants into a @T@ first.
module Keel.Asm (Reg (..), Operand (..), Cond (..), Width (..), BinOp (..), Asm (..)) where

data Reg = A Int | T Int | Sp
  deriving (Eq, Show)

data Operand = R Reg | I Integer
  deriving (Eq, Show)

-- | Compare-and-branch conditions (signed: @Lts@, @Ges@; the rest unsigned or equality).
data Cond = Eq | Ne | Ltu | Geu | Gtu | Leu | Lts | Ges
  deriving (Eq, Show)

-- | A memory access: a byte (zero-extended), the low 32 bits (sign-extended or not), or a
-- word (8 bytes, or 4 on RV32). The header and the runtime's variables are 8 bytes apart on
-- every target; RV32 uses the low word of each.
data Width = Byte | Half32 Bool | Word
  deriving (Eq, Show)

data BinOp = Add | Sub | And | Or | Xor | Shl | Shr | Sar
  deriving (Eq, Show)

data Asm m = Asm
  { wordBytes :: Int
  , mov :: Reg -> Operand -> m ()
  , -- | Three-address: @op o d a b@ is d = a o b. On x86 d must not be b unless it is a.
    op :: BinOp -> Reg -> Reg -> Operand -> m ()
  , -- | @load w d base off@, @store w v base off@.
    load, store :: Width -> Reg -> Reg -> Int -> m ()
  , -- | @loadIx d base i k@: d = word at base + i << k (d ≠ base). @storeIx v base i k tmp@.
    loadIx :: Reg -> Reg -> Reg -> Int -> m ()
  , storeIx :: Reg -> Reg -> Reg -> Int -> Reg -> m ()
  , -- | @addScaled d a b k@: d = a + b << k (d ≠ a).
    addScaled :: Reg -> Reg -> Reg -> Int -> m ()
  , -- | Compare and branch. Conditional branches on RISC-V reach ±4 KiB, so a target outside
    -- the routine (no local-label prefix) goes through an inverted branch over a jump.
    branch :: Cond -> Reg -> Operand -> String -> m ()
  , -- | @branchBit set n r tmp l@: to l if bit n of r is set (or clear).
    branchBit :: Bool -> Int -> Reg -> Reg -> String -> m ()
  , -- | @lowBit d s tmp@: d = the index of the lowest set bit of s (s ≠ 0, unchanged).
    lowBit :: Reg -> Reg -> Reg -> m ()
  , jump, call :: String -> m ()
  , callReg :: Reg -> m ()
  , ret :: m ()
  , addr :: Reg -> String -> m ()
  , -- | Increment the statistics counter at this byte offset of @_keel_stats@ (two temps).
    stat :: Int -> Reg -> Reg -> m ()
  , -- | A frame of n 8-byte slots, the return address saved; @slot i@ is slot i's offset from
    -- 'Sp'. 'unframe' takes the same n.
    frame, unframe :: Int -> m ()
  , slot :: Int -> Int
  , -- | A runtime function (aligned, as 'Keel.AArch64.pruneRuntime' expects), a label.
    fn, label :: String -> m ()
  , -- | A routine's local label: @L_x@ on ARM (Mach-O), @.L_x@ on ELF.
    local :: String -> String
  , newLabel :: m String
  }
