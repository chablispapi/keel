# Keel vs Goose, C++ and Rust (2026-10-22)

`python3 bench/goose/compare.py GOOSE_CHECKOUT --sizes medium,large`: three of Goose's
benchmarks (github.com/aardappel/goose, `bench/`) ported to Keel, every row built and run on
the same M-series Mac (clang -O2, rustc -O, `goose -O2` to C then clang -O2). Best of 3 wall
clocks, peak RSS. Every row prints the same checksums. Compare rows within one run only: the
machine's load moves every number by up to 1.6× between runs.

| benchmark | keel | goose | best C++ | C++ new/delete | best Rust | Rust Box |
|---|---:|---:|---:|---:|---:|---:|
| sum 16M | 78 ms / 124 MB | 56 / 63 | 52 / 63 | – | 56 / 63 | – |
| sum 128M | 578 / 978 | 403 / 490 | 393 / 490 | – | 442 / 490 | – |
| tree 20 | 60 / 50 | 42 / 26 | 51 / 26 | 82 / 66 | 43 / 26 | 80 / 66 |
| tree 24 | 874 / 770 | 622 / 386 | 747 / 386 | 1244 / 1030 | 642 / 386 | 2554 / 922 |
| bintrees 17 | 103 / 8 | 73 / 8 | 104 / 10 | 501 / 10 | 103 / 8 | 503 / 10 |
| bintrees 19 | 492 / 26 | 322 / 26 | 451 / 34 | 2351 / 34 | 452 / 28 | 2368 / 34 |

(sum rows rerun after array pushes grew in place. Previous run, before range analysis, the
register allocator and vectorizing: sum 16M 366 ms, tree 24 1508, bintrees 19 809.)

- **bintrees**: with each short-lived tree in an `arena`, level with C++ and Rust arenas at 17,
  1.1× behind at 19, 1.4–1.5× behind Goose; 4.8× faster than per-node allocation.
- **tree**: 1.4× faster than per-node C++ and Rust, 1.2–1.4× behind arenas and Goose. A node is
  32 bytes (header + three words) where Goose packs 12, so building and reading move 2× the
  memory, and peak memory is 2× theirs.
- **sum**: 1.3–1.5× behind. The scan is vectorized and close to memory bandwidth; a full
  array grows in place, so the array is the only memory (at 128M, 978 MB is the 1 GB array
  growing past its last doubling). What is left: i64 elements where the others use i32, so
  twice the bytes to write and read.

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
| a full unique array at the heap's top grows in place; push inline | (array growth) | sum 0.73×, memory 252 → 124 MB; sum 128M 2380 → 577 ms |

From the first measurement to the last: sum 16M 1329 → 366 ms, tree 24 1754 → 1508 ms,
bintrees 19 1716 → 809 ms.

## Next

Narrow fields (an `i32` field in 4 bytes) and a smaller header would close most of the tree
gap; for sum, i32 elements (arrays of one-word elements only, so far).
