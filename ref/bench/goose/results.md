# Keel vs Goose, C++ and Rust (2026-10-22)

`python3 bench/goose/compare.py GOOSE_CHECKOUT --sizes medium,large`: three of Goose's
benchmarks (github.com/aardappel/goose, `bench/`) ported to Keel, every row built and run on
the same M-series Mac (clang -O2, rustc -O, `goose -O2` to C then clang -O2). Best of 3 wall
clocks, peak RSS. Every row prints the same checksums. Compare rows within one run only: a
first run with the machine busier had the C++ and Rust per-node rows 2–3× slower.

| benchmark | keel | goose | best C++ | C++ new/delete | best Rust | Rust Box |
|---|---:|---:|---:|---:|---:|---:|
| sum 16M | 429 ms / 252 MB | 56 / 63 | 53 / 63 | – | 56 / 63 | – |
| sum 128M | 4881 / 1441 | 412 / 490 | 383 / 490 | – | 414 / 490 | – |
| tree 20 | 113 / 66 | 42 / 26 | 49 / 26 | 79 / 66 | 42 / 26 | 79 / 66 |
| tree 24 | 1754 / 1026 | 617 / 386 | 753 / 386 | 1207 / 1030 | 629 / 386 | 1335 / 1030 |
| bintrees 17 | 337 / 14 | 73 / 8 | 100 / 10 | 498 / 10 | 103 / 8 | 496 / 10 |
| bintrees 19 | 1514 / 50 | 316 / 26 | 448 / 34 | 2336 / 34 | 451 / 28 | 2278 / 34 |

- **bintrees** (allocate, check, free): Keel beats the per-node rows by 1.5×, and is 3–5×
  behind the arena rows and Goose. Freed blocks go to a free list, which beats malloc.
- **tree** (one big tree, read 8 times): ~1.4× behind per-node C++, ~3× behind arenas.
  `sumTree` takes the tree by value, so each visit adds and removes a reference on the node.
- **sum** (flat array loop): ~8–12× behind. The loop no longer touches reference counts
  (self tail calls are loops, and `let y = x` is an alias, not a second reference); what is
  left is code quality: every value goes through a register move or two, and every `+`
  checks for overflow. Memory: i64 elements where the others use i32, and a grown array's
  old blocks are not reused.

History: before self tail calls became loops and let-aliases stopped costing a reference,
sum 16M took 1329 ms.
