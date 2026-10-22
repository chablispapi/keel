# Keel compiler improvements

Priorities suggested by the current compiler notes and Keel–Haskell benchmarks.
These are candidates to investigate, not proven explanations for the timing gaps.

1. **Eliminate temporary allocations.** Remove pairs and other constructors that are
   immediately destructured, and avoid boxing values that never escape. Haskell's
   faster `churn` result suggests checking whether Keel can eliminate that pair entirely.
2. **Improve recursive list code.** Inspect allocation, reference counting, and generated
   calls in insertion sort, where Haskell won. Extend constructor reuse and remove
   redundant retain/release operations where ownership proves them unnecessary.
3. **Specialize capturing closures.** Extend specialization beyond closed functions to
   closures with captured values, reducing indirect calls and closure allocation.
4. **Improve register allocation.** Add live-range splitting so a value need not stay
   spilled for its entire lifetime; use spill measurements to guide the work.
   *Measured 2026-10-22:* no benchmark, example or test spills, except `balance` in
   `std/map.kl` (8 of 97 variables; 18 stack loads/stores in about 550 instructions, and it
   is not hot in any workload). Deferred until a workload spills.
5. **Optimize array-building loops.** Keep length and capacity in registers across pushes
   where safe, reducing repeated metadata loads and stores.
   *Measured 2026-10-22* (`sum`'s fill loop, 40M pushes): Keel 113 ms; C with length and
   capacity in registers 104 ms. Removing the per-push header check by hand gained nothing;
   replacing the `udiv` by 1000 gained 4%, so registers could buy at most ~4%. Deferred. The
   division is the larger part: `% k` by a constant still emits `udiv` (a multiply by a magic
   number would remove it), and propagating let-bound literals alone measured no gain.
6. **Pack tree data more tightly.** Investigate multiple narrow fields per word and
   arena-relative child offsets to reduce memory traffic and tree footprint.
   *Done 2026-10-22, all back ends:* block-relative 32-bit child offsets for constructors
   with two or more pointers; `tree` 24 514 → 386 MB and −7% time on ARM and x86-64,
   `bintrees` −23–30% memory. Two narrow fields per word was not pursued: no benchmark has
   a second narrow field.
7. **Strengthen the optimization pipeline.** Consider SSA and broader, cost-guided
   inlining when concrete missed optimizations justify them.

For each change, compare before/after assembly, time, and memory on the affected
benchmark, then check correctness on both ordinary and overflow/panic paths.
Preserve evaluation order and observable effects. Add workloads with capturing
closures and shared data before drawing broader performance conclusions.

Evidence: [performance notes](perf.md) and
[Keel vs Haskell results](../ref/bench/haskell/results.md).
