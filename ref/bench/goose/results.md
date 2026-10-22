# Keel vs Goose, C++ and Rust (2026-10-22)

`python3 bench/goose/compare.py GOOSE_CHECKOUT --sizes medium,large`: three of Goose's
benchmarks (github.com/aardappel/goose, `bench/`) ported to Keel, every row built and run on
the same M-series Mac (clang -O2, rustc -O, `goose -O2` to C then clang -O2). Best of 3 wall
clocks, peak RSS. Every row prints the same checksums.

| benchmark | keel | goose | best C++ | C++ new/delete | best Rust | Rust Box |
|---|---:|---:|---:|---:|---:|---:|
| sum 16M | 1329 ms / 252 MB | 67 / 63 | 57 / 63 | – | 60 / 63 | – |
| sum 128M | 11504 / 1599 | 538 / 490 | 502 / 490 | – | 510 / 490 | – |
| tree 20 | 130 / 66 | 46 / 26 | 55 / 26 | 107 / 66 | 51 / 26 | 86 / 66 |
| tree 24 | 2028 / 1026 | 706 / 386 | 951 / 386 | 3542 / 600 | 745 / 386 | 3463 / 568 |
| bintrees 17 | 383 / 14 | 80 / 8 | 113 / 12 | 578 / 10 | 110 / 10 | 547 / 10 |
| bintrees 19 | 1716 / 50 | 348 / 26 | 550 / 34 | 2696 / 34 | 568 / 28 | 2968 / 34 |

Keel beats the per-node-allocation rows (C++ new/delete, Rust Box) on the trees, and loses
to every arena row and to Goose by 3–5×. On the flat array loop it is ~20× behind: each
iteration of `scan` does two reference-count increments and two calls to `_keel_drop`,
because `array.length` and `array.get` consume the array and the loop must keep a reference
(M4: no borrowing for reads, no dup/drop cancellation). Turning self tail calls into loops
(after this table) removed the per-iteration save and restore of ten registers but changed
`sum` by under 2%; `bench/loop.kl`, which has no reference counting, got 1.9× faster. Memory: Keel stores i64
elements where Goose stores i32, and a grown array's old blocks are not reused.
