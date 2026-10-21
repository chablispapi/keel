# Keel native performance (M4)

Benchmarks are in `ref/bench/` and run with `ref/bench/run.sh`. It builds each program for ARM64
with `keelc` and reports the best of 5 wall-clock runs on the development Mac (Apple Silicon).
Every number is a full process run: startup, the computation, and freeing the heap.

| Benchmark | What it stresses | M3 | + known-arity calls | + register allocation | + specialization on dictionaries | + on functions | Speedup |
|---|---|---|---|---|---|---|---|
| `loop` | 200M iterations of a two-parameter tail-recursive loop | 1566 ms | 635 ms | 354 ms | 355 ms | 355 ms | 4.4× |
| `sort` | two insertion sorts of 3,000 elements, dictionary passing | 507 ms | 206 ms | 218 ms | 151 ms | 153 ms | 3.3× |
| `churn` | 10M pair allocations and frees | 113 ms | 77 ms | 66 ms | 66 ms | 66 ms | 1.7× |
| `map` | 1,000 in-place maps over 1,000 elements | 24 ms | 18 ms | 18 ms | 18 ms | 16 ms | 1.5× |
| `fib` | fib 32: about 7M non-tail calls | 20.7 ms | 19.1 ms | 16.7 ms | 17.3 ms | 16.2 ms | 1.3× |

## What changed

**Known-arity calls (uncurrying).** A top-level definition `def f = \x y. …` gets a second entry
point that takes all its parameters in registers (`x1`–`x7`, `a1`–`a7` on RISC-V). A call that
supplies all of them, `f a b`, goes straight there. Before, `f a` built a closure on the heap,
the call consumed it, and reference counting freed it, on every iteration of `loop`. The curried
entry point remains for partial applications and for `f` passed as a value. Evaluation order is
unchanged: applying only some arguments has no effect besides building a closure.

**Register allocation.** In each function, the most-used variables each get their own
callee-saved register (`x19`–`x28`, `s1`–`s11`) for the whole function, saved in the prologue
and restored before each return or tail call. The rest stay in stack slots. Every callee
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

Both back ends (ARM64 and RISC-V) share the allocation (`allocate` in `ref/src/Keel/AArch64.hs`),
and the full test suite passes on both after each step.

## Where the time still goes

- **Arguments that aren't constants**: specialization only fires for top-level cocases and
  functions, and for closed λs. A λ that captures a local variable, or a dictionary built at
  run time, is still called through a closure.
- **Register allocation is per function, not per live range**: one variable per register, so
  functions with more than 10 hot variables spill. A liveness-based allocator (linear scan) would
  share registers between variables that are never live at the same time.
- **Inlining is limited** to calls of small non-recursive top-level definitions and known
  observations (including lifted λs after specialization).
- **Reference counting is not optimized**: every field read is a dup and every case a drop.
  Borrowing parameters, and cancelling a dup against a drop of the parent when it is unique,
  are the standard Perceus refinements (`spec/memory.md`).

## Not done from the M4 roadmap

SSA form, a liveness-based register allocator, specializing on λs that capture locals
(defunctionalization), and our own Mach-O/ELF writers (`cc`, `clang` and
`ld.lld` still assemble and link). These are the remaining M4 items.
