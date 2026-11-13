# Proposal: high-assurance Keel (the ground Ada and SPARK hold)

## The problem

Ada and SPARK are used where a program has to be shown correct before it runs: avionics, rail,
medical devices, security firmware. Keel already proves several of the things those projects
need, and proves them in types, where SPARK needs separate contracts:
- `!Alloc`: no heap use, checked through every call (`spec/core.md` §5).
- No `Diverge`: the code terminates, by structural recursion (`spec/core.md` §2.4).
- No `Panic`: nothing aborts.
- An effect missing from a function's type (`MMIO`, `Hart`, `Shared`): the function never touches
  that resource (Theorem 4).
- Linear values are released exactly once (§1.5, proved in `proofs/`).

Four things are still missing, and each blocks a real use:
1. **Value constraints.** Ada's `range 0 .. 50_000` states what a value may be. With such
   constraints, SPARK proves that no runtime check fails. Keel's `Keel.Range` already removes
   checks it can prove, but that is an optimization: the type still says `Panic`, so a program
   can't promise "no overflow".
2. **Stack bounds.** `def interrupt` runs on the interrupted stack. Even without `Diverge`, a
   structurally recursive function uses stack in proportion to its input, so nothing bounds the
   stack it needs.
3. **More than one interrupt priority.** There is exactly one handler, and its only link to
   `main` is a queue. Ravenscar programs, and RTIC programs in Rust, are sets of prioritized tasks
   that share state without deadlocks.
4. **A Cortex-M target.** Most certified embedded code runs on Arm microcontrollers, and the Pico
   2's other two cores are Cortex-M33s.

The steps below are ordered by value per effort. Each fits the existing pattern: a label that is
implied and forbidden with `!`, or a check the elaborator removes before Keel Core, so the
metatheory and the Agda proofs need little or no change.

## Steps

### Step 1: range types, so the type checker can show that no check fails

```
type Altitude = u16 in 0 .. 50000
type Index    = usize in 0 .. 63
```

- **Declaring and converting.** A range type is a new name over an integer base type ι and a
  closed interval inside ι's range. It is `Free` and stored like ι. Values come into it only
  through `e as R` or a literal that fits. The conversion is checked: it has the effect `Panic`
  unless the interval of `e` (below) already fits inside R, in which case it has no effect.
  Conversions out (`e as ι'`) behave as they do today.
- **Arithmetic.** It is computed on intervals in the checker, the way Ada computes it on base
  types. For `a + b` with `a : R₁` and `b : R₂`, the result's interval is `[lo₁+lo₂, hi₁+hi₂]`.
  - If that interval fits ι, the operation can't overflow: it has **no `Panic`**, and its result
    has the base type ι with that interval known.
  - Otherwise it is checked, as today.
  - `*` uses the four corner products; `-` uses `[lo₁−hi₂, hi₁−lo₂]`. Literals have single-point
    intervals.
  - Plain ι values have ι's full interval, so existing code type-checks as before.
- **What inference tracks.** Intervals live in inference, not in Keel Core. Each integer-typed
  local has an interval, refined only by range types and literals. The checker deliberately
  doesn't learn from branches (`if x < 10`). That keeps types predictable; `Keel.Range` still
  removes checks after the branches as an optimization.
- **Elaboration.** It removes range types before Keel Core:
  - R becomes ι.
  - A proven-safe `+ - *` becomes `+% -% *%`. The two agree whenever no overflow can happen, and
    the wrapping forms already have effect `{}` in λK₂.
  - A checked `as R` becomes `if lo <= x && x <= hi then x else panic`.

  Core, the checker and the Agda development are unchanged.
- **Arrays.** `getAt`/`setAt` on a cell `[τ; n]` with an index of type `usize in 0 .. n−1`
  drop their bounds check and their `Panic`. Growable `Array a` has no static length, so it keeps
  its check; that case is left to refinements (Deferred).
- **Error messages.** Name the operation and both intervals, for example
  `a + b can overflow u16: 0..50000 + 0..50000 reaches 100000; this makes the function Panic`.
  Add it to the skill's table.
- **Files:**
  - `ref/src/Keel/Parser.hs` and `ref/selfhost/parser.kl` (the `type … in …` declaration).
  - Inference, which tracks intervals beside types.
  - `Keel.Elab`, which does the rewrite.
  - `spec/surface.md` (Types).

**Done when:** `test/assurance/ranges.kl`, a PID controller over range-typed sensor values,
type-checks as `->{!Alloc} …` with no `Panic`. Changing one range by one value makes the
checker report the overflow.

### Step 2: the `Recurse` effect and static stack bounds

- **The `Recurse` label.** It is built in, with no operations, and can't be handled, like
  `Alloc`. Every arrow implies it, and `!Recurse` forbids it.
  - A term has `Recurse` when it refers to a member of its own recursive group, using the group
    graph that `Termination.hs` already builds.
  - A self tail call doesn't count, since it compiles to a loop.
  - So `!Recurse` code has an acyclic call graph, apart from loops, and its stack depth is a
    finite sum of frame sizes.
- **`keelc stack FILE`.**
  - Each back end records every function's frame size, which it already knows when it emits
    the prologue.
  - The tool prints, for every `!Recurse` definition, the deepest path through the call graph and
    its total in bytes on each target, plus the trap frame for `interrupt`.
  - Indirect calls through closures or codata whose targets are unknown make the bound
    unavailable; the tool names them rather than guessing.
  - Calls into runtime routines count with the runtime's own bound. `_keel_drop` recurses into
    every pointer child except the last (`ref/src/Keel/Runtime.hs:461`), so its stack is
    unbounded. That is one more reason the bounded code is the `!Alloc` code.
- **Required for interrupts.** `def interrupt` must be `!Recurse`. The compiler then checks that
  `main`'s deepest bounded path plus the handler fits the stack the linker script reserves, on
  the freestanding targets.
- **Files:** `Termination.hs` (the group check is shared), `spec/core.md` §5 (the label, beside
  `Alloc`), `spec/surface.md` (Types, Interrupt handlers), and the three back ends plus
  `Keel.Runtime` for frame sizes.

**Done when:** `keelc stack test/firmware/interrupt.kl` prints bounds that QEMU confirms: the
test fills the stack with a canary pattern and checks the high-water mark it reaches against the
printed bound, on RV32 and RV64.

### Step 3: prioritized tasks with ceiling locks (Ravenscar / RTIC on Keel)

This replaces the single handler with tasks, keeping the old form as sugar.

```
task uart  : priority 2 on irq 10 = \u. …     -- ->{MMIO, Shared, !Alloc, !Recurse} Unit
task timer : priority 1 on irq 7  = \u. …
cell level : u32 = 0
```

- **Tasks.** Each one is `!Alloc`, `!Recurse` and has no `Diverge`, so its stack and termination
  are known. The runtime maps priorities onto the PLIC's priority and threshold registers on
  RISC-V. On Cortex-M (Step 4) it uses the NVIC.
- **Locks.** From the tasks' `Shared` accesses, the compiler computes each cell's **ceiling**:
  the highest priority of any task that uses it. A task that uses a cell whose ceiling is above
  its own priority must reach it inside `lock level (\u. …)`, which raises the threshold to the
  ceiling for that block. This is the Stack Resource Policy: no data races, no deadlock and at
  most one blocking per task, all by construction. A missing `lock` is a type error that names
  the cell, its ceiling and the higher-priority task.
- **Queues stay as they are.** They carry messages between tasks and `main`, and their
  single-writer argument (`spec/surface.md`, Queues) carries over per priority.
- **One core only.** Atomic counts and ownership transfer are for later (`spec/memory.md`).
- **Files:** a new elaboration pass that computes ceilings, the RISC-V runtime (the trap
  handler dispatches on `mcause` to tasks), and `spec/surface.md`.

**Done when:** `test/firmware/tasks.kl` runs two timers at different priorities that share a
counter. QEMU shows that preemption happens and that no update is lost, and a variant without
`lock` is rejected.

### Step 4: a Thumb-2 back end for Cortex-M

- **The back end.** Add a fourth back end through the portable assembler (`spec/backends.md`).
  Thumb-2 is 32-bit, and RV32 already covers the 32-bit `usize`, narrow fields and two-word
  integers.
- **Testing.** Run it under QEMU `mps2-an505` (Cortex-M33) in `cabal test all`, comparing with
  the evaluator and checking `live=0`, as RISC-V does.
- **Hardware.** Then run it on the Pico 2's Arm cores with the existing RP2350 boot image work:
  blink GP25.
- **Interrupts.** The NVIC gives Step 3 real hardware priorities, without the PLIC threshold
  dance.

**Done when:** the native suite passes on `--target thumbv8m` under QEMU and the blink example
runs on the board.

## Deferred

- **Contracts and refinements checked by SMT** (`{ i : usize | i < length xs }`, pre- and
  postconditions). Range types cover most of what SPARK's push-button proofs are used for. Add
  refinements when a real program needs a relation between two runtime values.
- **`Secret a` constant-time typing** for crypto (`notes.md` §14).
- **Heap bounds:** arenas sized at compile time, so running out of memory is impossible rather
  than a `Panic`.
- **Translation validation** of keelc's output, then tool qualification evidence (DO-178C,
  EN 50128). These are a matter of process and years, not one proposal.
- **Multicore:** atomic counts, or ownership transfer between cores.

## Verification

Each step adds its own `test/assurance/` or `test/firmware/` cases to `cabal test all`, and each
syntax change goes into both parsers. Steps 1 and 2 also add their wrong-program cases (an
overflow the checker must find, a recursive interrupt handler) with the compiler's exact
messages to the skill's mistakes table. `spec/core.md` changes only in §5 (the `Recurse`
label). It needs no new Agda proof, since `Recurse`, like `Alloc`, is a label with no operations.
