# Proposal: a portable assembler for the three back ends

Status: in progress, 2026-11-11 (proposed 2026-11-09; revised after a review against the code).

## The problem

`AArch64.hs`, `X86.hs` and `RiscV.hs` are 7,250 of the compiler's 13,600 lines, and every
change is ported three times. The duplication is in two places:

| Part | Lines per target | State |
|---|---|---|
| Runtime: the 13 shared routines (alloc, arenas, drop, free, reuse, arrays, perform) | ~615 ARM, ~610 x86, ~750 RISC-V | The same routines, translated by hand, same comments |
| Runtime: the rest (host I/O and sockets; RISC-V printing, traps, 64-bit arithmetic) | ~450 | Target-specific; stays where it is |
| Code generation (`expr`, `rhsCode`, `rhsInto`, `arith`, `moves`) | ~700–900 | Same case structure, different instructions and peepholes |
| Register allocation, layouts, headers, constants, runtime pruning | 0 (shared) | Already shared: X86 and RiscV import them from `Keel.AArch64` |

The 13 routines are the most mechanical part: loads, stores, arithmetic, compare-and-branch
and calls. They are not line-by-line translations, though. They differ in register use (ARM's
`_keel_arena_open` uses x9–x16, x86's `_keel_drop` saves rbx and r12, RISC-V's keeps values in
stack slots) and in small choices (ARM's `csel` where the others branch). Code generation is
where the per-target tuning lives (fused compare-and-branch, scaled addressing, RV32 register
pairs), so it is the riskier part to unify.

## The abstraction: a portable assembler, not an IR

A record of instruction emitters that each target fills in, and the runtime written once
against it. No IR datatype and no passes: the output is still assembly text through each back
end's `G` monad, so `pruneRuntime`, `line`, `ins` and `newLabel` keep working. The three `G`s
have different states, so the record carries the label operations too.

`ref/src/Keel/Asm.hs`, roughly:

```haskell
data Reg = A Int | T Int | Sp            -- arguments/result, scratch, stack pointer
data Operand = R Reg | I Integer
data Cond = Eq | Ne | Ltu | Geu | Gtu | Leu | Lts | Ges | BitSet Int | BitClear Int
data Width = Byte | Half32 Bool | Word | Dword    -- Half32: signed or not; Dword: 8 bytes everywhere
data BinOp = Add | Sub | And | Or | Xor | Shl | Shr | Sar

data Asm m = Asm
  { wordBytes :: Int
  , mov :: Reg -> Operand -> m ()
  , op, op32 :: BinOp -> Reg -> Reg -> Operand -> m ()        -- op32: on the low 32 bits
  , neg :: Reg -> Reg -> m ()
  , lowBit :: Reg -> Reg -> m ()                              -- index of the lowest set bit
  , load, store :: Width -> Reg -> Reg -> Int -> m ()         -- value, base, byte offset
  , loadIx, storeIx :: Width -> Int -> Reg -> Reg -> Reg -> m ()  -- base + index * scale
  , branch :: Cond -> Reg -> Operand -> String -> m ()        -- compare and branch
  , jump, call :: String -> m ()
  , callReg :: Reg -> m ()
  , ret :: m ()
  , addr :: Reg -> String -> m ()                             -- address of a symbol
  , stat :: Int -> m ()                                       -- increment a statistics counter
  , frame, unframe :: Int -> m ()                             -- n 8-byte slots at Sp
  , fn, label :: String -> m ()
  , local :: String -> String                                 -- L_x on ARM, .L_x elsewhere
  , newLabel :: m String
  }
```

The choices that matter:

- **Compare-and-branch is one operation**, so flags are never modelled. RISC-V emits `bxx`,
  ARM `cmp` + `b.cc` (`cbz` for `I 0`, `tbz`/`tbnz` for `BitSet`/`BitClear`), x86 `cmp`/`test`
  + `jcc`. RISC-V's conditional branches reach only ±4 KiB, so its emitter goes through
  `jumpIf` for targets outside the routine (the `_keel_panic_*` labels).
- **Three-address `op`**; x86 emits a `mov` first when the destination differs.
- **`A` and `T` never overlap.** Shared code may write a `T` and then read an `A`; on x86 the
  first draft's T set (rcx, rdx, rsi, rdi) contained `A 1` = rdi and `A 2` = rsi.

  | | `A 0..2` | `T 0..` (the first four are what `_keel_alloc` and `_keel_free_block` may clobber) |
  |---|---|---|
  | ARM | x0–x2 | x13–x16, then x9–x12 |
  | x86-64 | rax, rdi, rsi | rcx, rdx, r10, r11, then r8, r9 |
  | RISC-V | a0–a2 | t4–t6, a6, then t0–t3 |

  On x86 this moves `_keel_alloc`'s clobbers from rsi to r10/r11. r10 and r11 hold operands
  that are always consumed before an allocation; r8 still survives it, which the `Optional`
  overflow path relies on (it keeps the result there across the allocation of its box).
- **The header is 8 bytes on every target**, and so is the spacing of the runtime's variables
  and of the free-list table, even on RV32 (which uses each slot's low word). Array elements
  and fields are word-sized. So offsets are given in bytes, `loadIx`/`storeIx` take a scale,
  and `Dword` means 8 bytes; on RV32 the emitter reads or writes the low word of it.
- **Values that live across a nested call go in `frame` slots**, as RISC-V already does. ARM's
  register allocator relies on the runtime never touching callee-saved registers
  (`AArch64.hs`, `allocate`), and on x86 this removes `_keel_drop`'s rbx/r12 saves.
- **No hidden temporary register.** An emitter calls `error` on an immediate its target can't
  encode (ARM's logical immediates, RISC-V's 12 bits, x86's 32), and the shared code moves a
  large constant into a `T` first. The runtime is fixed, so any test run catches a mistake,
  and no routine gains a clobber.
- **`_keel_perform` is shared up to the machine.** The handler-frame scan is common; what an
  unhandled operation does (libc calls gated on the operations the program performs on ARM
  and x86, `_keel_handled` and its callers on RISC-V) stays in each back end, as a hook.
- RV32-only steps stay inline as `when (wordBytes asm == 4)`, as `RiscV.hs` does today. The
  routines that exist on one target only (host I/O, sockets, RISC-V printing, 64-bit multiply
  and divide, traps) stay where they are.

## Steps

1. Add `Keel/Asm.hs` and one `Asm G` value in each back end, built from its existing `ins`,
   `line`, `address`, `li` and `jumpIf`.
2. Pilot: write `_keel_arena_open` once in a new `Keel/Runtime.hs`, call it from all three
   `emitRuntime`s, delete the three originals.
3. Port the remaining routines one at a time in this order: `_keel_arena_close`, `_keel_alloc`,
   `_keel_free_block`, `_keel_drop`, `_keel_drop_reuse`, the six `_keel_array_*`, the
   `_keel_perform` scan. Run the suite after each.
4. Measure, then stop. Decide on code generation only with these numbers in hand.

Expected result: about 1,975 lines of runtime become about 650 shared plus about 450 of
emitters, a cut of about 850 lines. The main gain is that a runtime change is made once. The
estimate is from line counts, not from a trial port.

## Deferred

- **Unifying `expr`/`rhsCode`.** The same record could carry it later, with per-target hooks
  for the fused patterns. It needs the runtime port to prove the record first.
- **An IR datatype with passes.** Worth it when a pass needs it: RV32 64-bit legalization
  (now `primWide`/`arithWide` by hand) or item 7 of
  [compiler-improvements.md](compiler-improvements.md) (SSA).
- **Moving the shared helpers out of `AArch64.hs`.** A pure rename; do it if it gets in the way.
- **The runtime in Keel.** Not yet possible: `MMIO` has only 8- and 32-bit accesses, and only on
  freestanding RISC-V; there is no way to name a runtime global's address, find the lowest set
  bit or call a raw closure pointer; and compiled Keel functions don't keep `_keel_alloc`'s
  narrow clobber contract, so every allocation would become a full call. A word-sized memory
  effect on every target and a runtime calling convention would make the shared routines
  candidates for rewriting in Keel.

## Verification

- `cd ref && cabal test all` with `KEEL_X86_HOST` set, after every routine: native against
  the evaluator, `live=0`, RISC-V under QEMU (RV64 and RV32), x86-64 over ssh.
- `keelc asm` (AArch64 only) on `ref/bench/*.kl` before and after each routine. The output is
  not byte-identical (registers and routine order change), but every difference in the runtime
  section should be explainable.
- `ref/bench/run.sh` and `ref/bench/goose/compare.py` (with `--host` for x86-64) before the
  pilot and after the last routine. `_keel_alloc` and `_keel_drop` are hot, so a slowdown
  beyond noise there means the record needs a wider operation, not that the port should stand.
