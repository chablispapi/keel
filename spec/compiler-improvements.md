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
5. **Optimize array-building loops.** Keep length and capacity in registers across pushes
   where safe, reducing repeated metadata loads and stores.
6. **Pack tree data more tightly.** Investigate multiple narrow fields per word and
   arena-relative child offsets to reduce memory traffic and tree footprint.
7. **Strengthen the optimization pipeline.** Consider SSA and broader, cost-guided
   inlining when concrete missed optimizations justify them.

For each change, compare before/after assembly, time, and memory on the affected
benchmark, then check correctness on both ordinary and overflow/panic paths.
Preserve evaluation order and observable effects. Add workloads with capturing
closures and shared data before drawing broader performance conclusions.

Evidence: [performance notes](perf.md) and
[Keel vs Haskell results](../ref/bench/haskell/results.md).
