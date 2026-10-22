# Keel vs Goose, C++ and Rust (2026-10-22)

`python3 bench/goose/compare.py GOOSE_CHECKOUT --sizes medium,large`: three of Goose's
benchmarks (github.com/aardappel/goose, `bench/`) ported to Keel, every row built and run on
the same M-series Mac (clang -O2, rustc -O, `goose -O2` to C then clang -O2). Best of 3 wall
clocks, peak RSS. Every row prints the same checksums. Compare rows within one run only: the
machine's load moves every number by up to 1.6× between runs.

| benchmark | keel | goose | best C++ | C++ new/delete | best Rust | Rust Box |
|---|---:|---:|---:|---:|---:|---:|
| sum 16M | 366 ms / 252 MB | 59 / 63 | 57 / 63 | – | 58 / 63 | – |
| sum 128M | 4695 / 1296 | 422 / 490 | 429 / 490 | – | 430 / 490 | – |
| tree 20 | 97 / 50 | 47 / 26 | 53 / 26 | 86 / 66 | 49 / 26 | 83 / 66 |
| tree 24 | 1508 / 770 | 631 / 386 | 802 / 386 | 1879 / 1030 | 628 / 386 | 1298 / 1030 |
| bintrees 17 | 143 / 8 | 74 / 8 | 101 / 10 | 503 / 10 | 104 / 8 | 503 / 10 |
| bintrees 19 | 809 / 26 | 347 / 26 | 457 / 38 | 2491 / 34 | 500 / 28 | 2493 / 34 |

- **bintrees**: with each short-lived tree in an `arena`, 3× faster than per-node allocation in
  C++ and Rust and 1.6–1.8× behind their arenas and Goose, at the same peak memory as Goose.
- **tree**: level with per-node C++ and Rust, 2.4× behind arenas and Goose. A node is 32 bytes
  (header + three words) where Goose packs 12, so building and reading move 2× the memory.
- **sum**: 6–11× behind. The loop does no reference counting; what is left is code quality
  (the loop is ~15 instructions where clang vectorizes 4 elements at a time: moves and a spill
  at the back edge, the length loaded twice), i64 elements where the others use i32, and a
  grown array's old blocks are not reused. The overflow checks cost nothing measurable: with
  `+%` the loop runs at the same speed, and range analysis (below) removes all but `acc + x`'s.

## What each change did

Measured A/B: the compiler before and after the change, runs alternating, best of 5. Ratios
are time after / time before (sum at 16M elements, tree at depth 24, bintrees at depth 19;
`bench/loop.kl` is a counting loop).

| change | commit | effect |
|---|---|---|
| self tail calls are loops | 1fb84b9 | loop 0.53×; sum 0.98× |
| `let y = x` is an alias, not a second reference | 1c3a75e | sum 0.32× (1329 → 429 ms) |
| borrowed parameters, inferred | f15cdd6 | tree 0.88×, bintrees 0.88× |
| constructors without fields are shared static blocks | 03680f6 | bintrees 0.88×, memory 50 → 34 MB |
| the constructor tag in the header | a6582f0 | bintrees 0.74×, tree 0.96× |
| AArch64 operands in registers, compare-and-branch | 9c982d7 | sum 0.84×, loop 0.73× |
| arenas (`arena (\u. e)`) in the bintrees port | b350761 | bintrees 0.55× |
| range analysis: unneeded overflow and bounds checks removed | `Keel.Range` | all 1.00× |
| registers by graph colouring, self tail calls as parallel moves | (next) | sum 0.45×, tree 0.59×, bintrees 0.71×, fib 0.71× |

From the first measurement to the last: sum 16M 1329 → 366 ms, tree 24 1754 → 1508 ms,
bintrees 19 1716 → 809 ms.

## Next

Narrow fields (an `i32` field in 4 bytes) and a smaller header would close most of the tree
gap; for sum, keeping loop variables in registers across the back edge (no spills, no moves
for the self call), then vectorizing with one overflow check per loop instead of per add.
