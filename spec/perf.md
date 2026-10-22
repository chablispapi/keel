# Keel native performance (M4)

Benchmarks are in `ref/bench/` and run with `ref/bench/run.sh`. It builds each program for ARM64
with `keelc` and reports the best of 5 wall-clock runs on the development Mac (Apple Silicon).
Every number is a full process run: startup, the computation, and freeing the heap.

For a fresh comparison against strict Haskell ports of these five workloads and the
larger sum/tree/binary-trees workloads, see [Keel vs Haskell](../ref/bench/haskell/results.md)
(runner, compiler flags, raw samples, and allocation caveats included).

| Benchmark | What it stresses | M3 | + known-arity calls | + register allocation | + specialization on dictionaries | + on functions | Speedup |
|---|---|---|---|---|---|---|---|
| `loop` | 200M iterations of a two-parameter tail-recursive loop | 1566 ms | 635 ms | 354 ms | 355 ms | 355 ms | 4.4× |
| `sort` | two insertion sorts of 3,000 elements, dictionary passing | 507 ms | 206 ms | 218 ms | 151 ms | 153 ms | 3.3× |
| `churn` | 10M pair allocations and frees | 113 ms | 77 ms | 66 ms | 66 ms | 66 ms | 1.7× |
| `map` | 1,000 in-place maps over 1,000 elements | 24 ms | 18 ms | 18 ms | 18 ms | 16 ms | 1.5× |
| `fib` | fib 32: about 7M non-tail calls | 20.7 ms | 19.1 ms | 16.7 ms | 17.3 ms | 16.2 ms | 1.3× |

These are historical measurements. Constructor elimination now removes the pair in `churn`
entirely: its current generated loop allocates no blocks.

## Full-field constructor reuse (AArch64, 2026-10-22)

When a `case` proves a constructor's layout and `DropReuse` transfers every pointer field,
the AArch64 emitter now tests the reference count inline. A unique parent becomes a reuse
token without calling `_keel_drop_reuse` or walking its children. Shared and immortal parents,
zero counts, unknown layouts and partial transfers retain the existing helper path. Header
fields, arena behavior and all allocator counters are preserved. This is instruction selection
only; Core optimizations, ownership inference, calling conventions and other targets are unchanged.

Paired baseline/candidate runs use the same compiler with only this specialization disabled
or enabled. After warmups, the runner alternates execution order for 15 repetitions, checks
every output and exit status, and compares allocator counters in separate untimed runs.
Numbers below are median full-process wall times, including `/usr/bin/time -l` launch overhead;
compilation and linking are excluded. Timing runs have `KEEL_STATS` unset, although both runtimes
still maintain their usual counters. Tests were finished before timing began.

| Workload | Helper baseline (ms) | Inline reuse (ms) | Baseline / candidate |
|---|---:|---:|---:|
| `loop` | 141.73 | 141.17 | 1.004× |
| `sort` | 93.97 | 84.20 | 1.116× |
| `churn` | 11.61 | 11.94 | 0.973× |
| `map` | 14.80 | 14.60 | 1.013× |
| `fib` | 26.45 | 25.82 | 1.024× |
| `sum-medium` | 86.66 | 85.28 | 1.016× |
| `tree-medium` | 48.55 | 48.99 | 0.991× |
| `bintrees-medium` | 105.34 | 105.39 | 1.000× |
| `sum-large` | 668.42 | 639.63 | 1.045× |
| `tree-large` | 704.07 | 724.45 | 0.972× |
| `bintrees-large` | 510.67 | 495.22 | 1.031× |

An independent 25-repetition run confirmed `sort` at 97.25 → 88.76 ms (1.096×), and `map`
at 15.14 → 14.76 ms (1.026×). The sort improvement repeats; the small map improvement is
less conclusive. All other workloads have no eligible reuse sites, so their timing differences
should not be attributed to this optimization. No measured slowdown exceeded 3%.

Every workload retained exactly the same allocation/recycle/reuse/free counts and ended with
`live=0`. Peak RSS was effectively unchanged (raw samples below). Sort's text section grew
from 5,480 to 5,672 bytes; map's grew from 3,860 to 3,908 bytes. Slow-path helper calls remain
in the assembly, guarded by the inline uniqueness check; the unique path contains no call.

Reproduce from the repository root on an AArch64 Mac:

```sh
cd ref
cabal build keelc
cd ..
python3 ref/bench/reuse.py --output /tmp/keel-reuse.json
python3 ref/bench/reuse.py --reps 25 --only sort,map --output /tmp/keel-reuse-confirmation.json
```

[Full raw results](../ref/bench/reuse-results.json) and
[confirmation results](../ref/bench/reuse-confirmation.json) include source revision/diff identity,
toolchain, all samples, peak RSS, code sizes and allocator counters. The Haskell entrypoint
`compileNativeWithReuse debug enabled` provides the comparison switch without a new CLI flag.
Native differential tests compare both emitted code and optimized Core against the original
elaborated program; focused tests also check helper equivalence and zero/immortal headers.
Validation: `cabal test core native --test-show-details=direct` passed 84 core, 209 native
and 115 RISC-V cases. Native coverage includes debug builds. The focused `x86Failures`
harness subsequently passed all 114 x86-64 cases with `KEEL_X86_HOST=chablis@192.168.0.167`,
checking outputs, panic results and zero live blocks on successful runs.

## What changed

**Known-arity calls (uncurrying).** A top-level definition `def f = \x y. …` gets a second entry
point that takes all its parameters in registers (`x1`–`x7`, `a1`–`a7` on RISC-V). A call that
supplies all of them, `f a b`, goes straight there. Before, `f a` built a closure on the heap,
the call consumed it, and reference counting freed it, on every iteration of `loop`. The curried
entry point remains for partial applications and for `f` passed as a value. Evaluation order is
unchanged: applying only some arguments has no effect besides building a closure.

**Register allocation.** Callee-saved registers (`x19`–`x28`, `s1`–`s11`), saved in the
prologue and restored before each return or tail call, assigned by colouring the interference
graph: variables live at the same time get different registers, so two that never are can
share one. Most-used variables are coloured first, and an argument of a self tail call prefers
its parameter's register; the jump back then moves the arguments into the parameters as one
parallel move, usually none at all. The rest stay in stack slots. Every callee
preserves these registers (Keel functions save what they use; the runtime and the C library
never touch them), so values survive calls without spilling around each one.

**Specialization and inlining** (`ref/src/Keel/Opt.hs`, after monomorphization). A call that
passes a top-level `cocase` constant, such as `sort ascending xs`, uses a copy of the function
with that parameter replaced by the constant; recursive calls pass it along and reach the same
copy. Then an observation of a known constant (`ascending.lt`) is replaced by its branch, small
non-recursive definitions are inlined, `(λx. b) a` becomes `let x = a in b`, and unreachable
definitions are removed. Top-level functions are constants too, and a closed λ argument is
first lifted to a top-level definition, so `map (\x. x + 1) xs` becomes a copy of `map` with the
addition inlined: `map[i64; i64; {Panic}]{0=lam'0}`, with no closure call per element. For
`sort` this leaves `sort[i64]{0=ascending}` and
`insert[i64]{0=ascending}` comparing with a plain `<`: the dictionary is gone at run time, which
is what notes.md §16 promised for explicit dictionaries + monomorphization. The optimized program
is type-checked again, and the test runner checks it computes the same result as the
unoptimized one on every test.

**Specialization on capturing λs** (`liftClosed` and `specialize` in `ref/src/Keel/Opt.hs`).
A λ argument that captures locals, `map (\x. x + k) xs`, is lifted to `lam'n = \k. \x. x + k`
and passed as the partial application `lam'n k`; the call then uses
`map{0=lam'n/1}`, a copy that takes `k` as a parameter in place of `f` and calls `lam'n k x`
directly, which the inliner removes. This happens only when the copy's parameter is only called
or passed along to the same position of a recursive call, so the copy never builds the closure
it replaces. A function the elaborator names before effectful arguments (`let a = map in a …`)
is now seen through, which also lets closed effectful λs specialize. `closure` (`map.kl` adding
each iteration's `k`): 12.8 → 10.9 ms (1.17×, median of 15 alternating runs), and one closure
per map fewer. The other benchmarks compile to identical assembly.

**Range analysis** (`ref/src/Keel/Range.hs`, on the lowered IR, both back ends). It tracks
intervals of integers and the relations `≤`, `<`, `≠` between variables, constants and array
lengths, from arithmetic and from the branches of comparisons. A function called only directly
gets parameter invariants: candidates (`0 ≤ p`, `p ≤ k` or `k ≤ p` for a constant it compares
`p` with, `p ≤ length q`) that every call proves, found by dropping the ones some call can't
prove until the rest hold. A checked `+ - *` whose result fits its type becomes a plain one,
and `array.get xs i` with `0 ≤ i < length xs` reads without the bounds check. In the `sum`
benchmark's loop this removes `i + 1`'s check and the bounds check; `acc + x` stays checked,
since nothing bounds the elements. No measurable speedup (the checks were never-taken branches
next to `adds`); fewer checks matter once loops are vectorized.

**Vectorized reductions** (AArch64 only, `vectorLoop` in `ref/src/Keel/AArch64.hs`). A loop of
the shape `f … xs i acc = if i == length xs then … else f … xs (i + 1) (acc + e)`, where `e` is
computed from `get xs i` (unchecked, by range analysis), unchanged parameters and constants with
64-bit `land lor lxor +% -%`, first runs four elements at a time in NEON registers, then the
scalar loop does the rest. For a checked `acc + e`, the vector result is kept only if every `e`
was ≥ 0 and no lane overflowed; the sum then only grows, so adding the lanes to `acc` with
checked adds panics exactly when the scalar loop would. Otherwise the scalar loop redoes those
elements, which is unobservable because the loop is pure. `sum` 0.64×; on an array that fits
in cache, the scan is 3.4× faster.

**Array growth** (AArch64). `array.push` on a full array that is unique and ends at the bump
pointer (nothing allocated after it) extends the block where it is instead of copying it into
one twice the size, which also leaves no old copy behind; a push with room in a unique array
stores without calling the runtime. `sum` 0.73× and half the memory; at 128M elements 4× faster.
RISC-V still copies.

**Narrow fields in the header** (both back ends, `spec/memory.md`). The header keeps the count and
a layout id in its low half; a data block's first field of at most 32 bits goes in the high
half, so `Leaf(i32)` is 8 bytes and `Node(i32, Box T, Box T)` 24 (was 16 and 32). `tree` at
depth 24 needs 513 MB instead of 768. That alone didn't change its time: the time was in calls
and in freeing 32M blocks one by one. Saving callee-saved registers in pairs (`stp`/`ldp`),
widening conversions as moves and letting a `case`'s last branch fall through gave 0.91×; the
port now keeps its tree in an `arena` (as Goose keeps its in one pool), 0.79× more. Reading the
layout costs one instruction more per `case` than the old tag byte (`map` 1.03×).

**4-byte array elements** (both back ends). `Array i32` (and `u32`, `u8`, `Bool`, …) stores
4 bytes per element, read sign- or zero-extended; the vectorized reduction loads eight such
elements per iteration and widens them to 64-bit lanes (`sxtl`/`uxtl`). `sum` ported to `i32`
elements: peak memory equal to Goose's (63 MB at 16M), 0.96× the time: what is left is
building the array (each push stores the length that the next one loads). Also: shifts by a
constant, division by a constant other than 0 and -1, and narrowing conversions are one or
two instructions with no checks.

Both back ends (ARM64 and RISC-V) share the allocation (`allocate` in `ref/src/Keel/AArch64.hs`),
and the full test suite passes on both after each step.

## Where the time still goes

- **Arguments that aren't constants**: specialization fires for top-level cocases and
  functions, closed λs, and λs that capture locals (below). A dictionary built at run time, a
  closure stored in data or returned, and one rebuilt by each recursive call (`twice (\x. f (f x))`)
  are still called through a closure; so is a capturing λ passed to an already specialized
  copy, whose recursive calls go to the original name.
- **Register allocation has no live-range splitting**: a variable that doesn't get a register
  stays in its stack slot everywhere, and values live across calls compete for the same 10.
- **Inlining is limited** to calls of small non-recursive top-level definitions and known
  observations (including lifted λs after specialization).
- **Reference counting has more opportunities**: borrowed parameters, borrowed fields and
  field-dup fusion with reuse are implemented, along with the AArch64 full-field fast path
  above. Ordinary parent drops still do not transfer field ownership, and partial transfers
  still use the generic reuse helper (`spec/memory.md`).

## Not done from the M4 roadmap

SSA form and our own Mach-O/ELF writers (`cc`, `clang` and
`ld.lld` still assemble and link). These are the remaining M4 items.
