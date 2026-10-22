# Keel vs Goose, C++ and Rust (2026-10-22)

`python3 bench/goose/compare.py GOOSE_CHECKOUT --sizes medium,large`: three of Goose's
benchmarks (github.com/aardappel/goose, `bench/`) ported to Keel, every row built and run on
the same M-series Mac (clang -O2, rustc -O, `goose -O2` to C then clang -O2). Best of 3 wall
clocks, peak RSS. Every row prints the same checksums. Compare rows within one run only: the
machine's load moves every number by up to 1.6× between runs.

| benchmark | keel | goose | best C++ | C++ new/delete | best Rust | Rust Box |
|---|---:|---:|---:|---:|---:|---:|
| sum 16M | 74 ms / 63 MB | 56 / 63 | 51 / 63 | – | 55 / 63 | – |
| sum 128M | 560 / 490 | 429 / 490 | 380 / 490 | – | 409 / 490 | – |
| tree 20 | 44 / 34 | 42 / 26 | 54 / 26 | 79 / 66 | 42 / 26 | 97 / 66 |
| tree 24 | 636 / 514 | 629 / 386 | 743 / 386 | 2487 / 872 | 619 / 386 | 2700 / 790 |
| bintrees 17 | 97 / 8 | 72 / 8 | 100 / 10 | 497 / 10 | 101 / 8 | 499 / 10 |
| bintrees 19 | 425 / 26 | 315 / 26 | 441 / 34 | 2329 / 34 | 448 / 28 | 2244 / 34 |

(sum rows from the run after i32 array elements, tree and bintrees after narrow fields.
The first run, before range analysis, the register allocator and vectorizing: sum 16M 366 ms,
tree 24 1508, bintrees 19 809.)

- **bintrees**: with each short-lived tree in an `arena`, level with or ahead of C++ and Rust
  arenas, 1.3–1.35× behind Goose; 5× faster than per-node allocation.
- **tree**: with the tree in an `arena`, level with Goose and Rust's arena, ahead of C++'s, 4×
  faster than per-node allocation. A node is 24 bytes and a leaf 8 (an `i32` in the header
  word) where Goose packs 12 with 32-bit offsets, so peak memory is 1.33× theirs.
- **sum**: 1.3× behind, at the same peak memory (i32 elements, 4 bytes each; the array grows in
  place). The eight scans are vectorized and take ~26 ms of the 74; the rest is building the
  array, where each push stores the length the next one loads back.

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
| registers by graph colouring, self tail calls as parallel moves | 986e6f4 | sum 0.45×, tree 0.59×, bintrees 0.71×, fib 0.71× |
| reductions over arrays vectorized (AArch64) | ed19a7a | sum 0.64× |
| a full unique array at the heap's top grows in place; push inline | 09a1d52 | sum 0.73×, memory 252 → 124 MB; sum 128M 2380 → 577 ms |
| narrow fields in the header (tree port: i32 values), paired register saves, tree in an `arena` | 4e9c24d | tree 0.71× (memory 770 → 514 MB), bintrees 0.95× |
| 4-byte array elements (sum port: i32), constant shifts and divisions | (i32 arrays) | sum 0.96× (memory 124 → 63 MB) |

From the first measurement to the last: sum 16M 1329 → 366 ms, tree 24 1754 → 1508 ms,
bintrees 19 1716 → 809 ms.

## Next

For tree's memory, 32-bit child references (offsets in the heap) and packing narrow fields
two to a word; for sum, keeping an array's length in a register across a loop of pushes.
