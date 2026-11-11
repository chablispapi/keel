# A portable assembler for the three back ends

Status: done for the runtime, 2026-11-11 (proposed 2026-11-09; revised after a review against
the code). Code generation is still per target; see [Deferred](#deferred).

## The problem

`AArch64.hs`, `X86.hs` and `RiscV.hs` were 7,250 of the compiler's 13,600 lines, and every
change was ported three times. The duplication was in two places:

| Part | Lines per target | State |
|---|---|---|
| Runtime: alloc, arenas, drop, free, reuse, arrays | ~615 ARM, ~610 x86, ~750 RISC-V | **Now shared** (`Keel.Runtime`) |
| Runtime: `_keel_perform`, host I/O and sockets; RISC-V printing, traps, 64-bit arithmetic | ~450 | Target-specific; stays where it is |
| Code generation (`expr`, `rhsCode`, `rhsInto`, `arith`, `moves`) | ~700–900 | Same case structure, different instructions and peepholes |
| Register allocation, layouts, headers, constants, runtime pruning | 0 (shared) | Already shared: X86 and RiscV import them from `Keel.AArch64` |

The runtime routines were the most mechanical part: loads, stores, arithmetic,
compare-and-branch and calls. They were not line-by-line translations, though. They differed in
register use (ARM's `_keel_arena_open` used x9–x16, x86's `_keel_drop` saved rbx and r12,
RISC-V's kept values in stack slots) and in small choices (ARM's `csel` where the others
branched). Code generation is where the per-target tuning lives (fused compare-and-branch,
scaled addressing, RV32 register pairs), so it is the riskier part to unify.

## The abstraction: a portable assembler, not an IR

`Keel.Asm` is a record of instruction emitters that each target fills in (`asmArm`, `asmX86`,
`asmRv`, next to each back end's `emitRuntime`), and `Keel.Runtime` writes the routines once
against it. There is no IR datatype and there are no passes: the output is still assembly text
through each back end's `G` monad, so `pruneRuntime`, `line`, `ins` and `newLabel` keep
working. The three `G`s have different states, so the record carries the label operations too.

The choices that matter:

- **Compare-and-branch is one operation**, so flags are never modelled. RISC-V emits `bxx`,
  ARM `cmp` + `b.cc` (`cbz`/`cbnz` against 0, `tbnz`/`tbz` for a sign test), x86 `cmp`/`test`
  + `jcc`. RISC-V's conditional branches reach only ±4 KiB, so its emitter goes through
  `jumpIf` for targets outside the routine (the `_keel_panic_*` labels).
- **Three-address `op`**; x86 emits a `mov` first when the destination differs, and shifts
  only by an immediate or by `T 0` (rcx).
- **`A` and `T` never overlap.** Shared code may write a `T` and then read an `A`; the first
  draft's x86 T set (rcx, rdx, rsi, rdi) contained `A 1` = rdi and `A 2` = rsi.

  | | `A 0..` | `T 0..` (the first four are all that `_keel_alloc` and `_keel_free_block` clobber) |
  |---|---|---|
  | ARM | x0–x2 | x13–x16, then x9–x12 |
  | x86-64 | rax, rdi, rsi | rcx, rdx, r10, r11, then r8, r9 |
  | RISC-V | a0–a3 | t4–t6, a6, then t0–t3 |

  On x86 this moved `_keel_alloc`'s clobbers from rsi to r10/r11. r10 and r11 hold operands
  that are always consumed before an allocation; r8 still survives it, which the `Optional`
  overflow path relies on (it keeps the result there across the allocation of its box).
- **The header is 8 bytes on every target**, and so is the spacing of the runtime's variables
  and of the free-list table, even on RV32 (which uses each slot's low word). Array elements
  and fields are word-sized. So offsets are in bytes and `loadIx` and `addScaled` take a shift.
  `Word` is 8 bytes, or 4 on RV32; RISC-V's `ins` already rewrites `ld`/`sd` to `lw`/`sw`.
- **The count is read as a sign-extended 32-bit value** and handled with ordinary word
  arithmetic: negative means immortal, `>> 10` is the count. That works the same on all
  three targets, so the record has no 32-bit operations.
- **Values that live across a nested call go in `frame` slots**, as RISC-V already did. ARM's
  register allocator relies on the runtime never touching callee-saved registers
  (`AArch64.hs`, `allocate`), and on x86 this removed `_keel_drop`'s rbx/r12 saves.
- **No hidden temporary register.** Where RISC-V needs one more register (a bit test, the
  lowest set bit, an indexed store, a statistics counter), the operation takes it as an
  argument and the other targets ignore it. An immediate the target can't encode is left to
  the assembler to reject (RISC-V's `branch` refuses any but 0), and the shared code moves
  large constants into a `T` first. No routine gained a clobber.
- **`loadSym`** loads the word at a symbol in one operation (x86's `mov [rip + …]`, ARM's
  `adrp` + `ldr`), so the hot paths in `_keel_alloc` and `_keel_drop` don't pay for an address
  followed by a load.
- **`_keel_perform` stays per target.** Its handler scan is about 25 lines, but each target's
  prologue is shared with the machine fallback below it: x86 saves rbx, r12 and r13 because
  the socket code keeps values in them across C calls, and ARM's socket code addresses locals
  off the frame set up there. Sharing the scan would take prologue, epilogue and machine hooks
  to save about 50 lines.
- RV32-only steps stay inline as `when (wordBytes a == 4)`. On RV32 a kind-1 array element is
  two words, its high half in the next argument register.

## Result

All twelve routines are written once in `Keel.Runtime`: `_keel_alloc`, `_keel_free_block`,
`_keel_drop`, `_keel_drop_reuse`, `_keel_arena_open`, `_keel_arena_close` and the six
`_keel_array_*`.

| | Before | After |
|---|---|---|
| `AArch64.hs` | 2,638 | 2,118 (emitter: 79) |
| `X86.hs` | 2,199 | 1,697 (emitter: 88) |
| `RiscV.hs` | 2,415 | 1,872 (emitter: 107) |
| `Asm.hs` + `Runtime.hs` | — | 70 + 789 |
| Total | 7,252 | 6,546 |

A net cut of 706 lines; the estimate was about 850, because the shared runtime came out at 789
lines against an expected 650. The main gain is that a runtime change is now made once.

Behaviour changes: RISC-V's `_keel_array_push` now grows a unique array at the end of the heap
in place, as ARM's and x86's already did. Everything else computes what it did before.

Speed, ARM64, best of 7, pre-port compiler against the final one: loop −0.1%, sort −0.8% (+1.6%
on a second run), tree +0.6%, bintrees −0.0%, sum −0.0% (+6.6% once, not reproduced). The
runs of 20–130 ms vary by about ±2% between identical binaries, and the 10 ms ones (churn,
closure, fib, map) by up to ±8%, which is process start-up. No slowdown beyond noise. The
generated `_keel_alloc` is one instruction longer (the size limit moves into a register,
since RISC-V can't compare with an immediate). x86-64 was not timed: `compare.py` needs a
Goose checkout.

## Deferred

- **Unifying `expr`/`rhsCode`.** The same record could carry it, with per-target hooks for the
  fused patterns. The runtime port shows the record works; the code generator has far more
  per-target tuning, so it would need the hooks designed first.
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
  the evaluator, `live=0`, RISC-V under QEMU (RV64 and RV32), x86-64 over ssh. It passed after
  each: core 104/104, native 284/284, RV64 157/157, RV32 140/140, x86-64 140/140.
- `keelc asm` (AArch64 only) before and after each routine. The output is not byte-identical
  (registers change, `stp`/`ldp` and `csel` become pairs of stores and branches), and each
  difference was read.
- A best-of-7 A/B on `ref/bench/*.kl` and `ref/bench/goose/{tree,bintrees,sum}.kl`, built by
  the pre-port compiler and the current one (ARM64).
