# Keel vs Haskell (2026-10-22)

All five existing microbenchmarks in `ref/bench/*.kl`, plus the medium and large sizes
of all three workloads in `ref/bench/goose/`, rebuilt and run together on this Apple Silicon
Mac (ARM64, macOS 27.0). Keel source commit: `d4a1f1c76f743ab224b2995e65804dcd7e3fdc49`.

The Glorious Glasgow Haskell Compilation System, version 9.10.3. Haskell flags: `-O2 -XFlexibleContexts -fno-full-laziness -fno-cse`.
Default single-capability GHC runtime settings; no RTS heap tuning. The Keel compiler was
rebuilt with `cabal build keelc` before this run.

Best of five full-process wall times after one warmup per binary, alternating execution
order each repetition. Peak RSS is the maximum across the five timed runs, in MiB.
Timing includes startup, output, and shutdown, but excludes compilation. Every warmup and
timed execution passed the output/checksum comparison. Raw samples are in `results.json`.

| Workload | Keel ms | Haskell ms | Haskell / Keel time | Keel MiB | Haskell MiB |
|---|---:|---:|---:|---:|---:|
| loop 200000000 | 131.1 | 139.7 | 1.07× | 1.6 | 11.2 |
| sort 3000 | 139.0 | 96.0 | 0.69× | 1.8 | 15.3 |
| churn 10000000 | 64.2 | 18.3 | 0.28× | 1.6 | 11.2 |
| map 1000 | 17.4 | 19.9 | 1.15× | 1.6 | 11.2 |
| fib 32 | 14.1 | 31.8 | 2.26× | 1.6 | 11.2 |
| sum 16000000 | 72.9 | 190.9 | 2.62× | 62.6 | 73.3 |
| tree 20 | 41.6 | 115.6 | 2.78× | 33.6 | 104.2 |
| bintrees 17 | 96.1 | 131.1 | 1.36× | 7.6 | 17.3 |
| sum 128000000 | 552.9 | 1414.4 | 2.56× | 489.8 | 500.3 |
| tree 24 | 584.3 | 1616.7 | 2.77× | 513.6 | 918.2 |
| bintrees 19 | 424.3 | 622.4 | 1.47× | 25.6 | 71.3 |

A time ratio above 1 means Keel was faster. These are workload results, not an overall
language ranking. Startup and process launch overhead matter for the shortest rows.

## Implementation choices

- Haskell uses strict recursive lists and trees, machine `Int` (64 bits here), `Word64`
  xorshift arithmetic, and `Int32` array/tree values, matching the Keel algorithms and sizes.
- Haskell uses a preallocated `IOUArray` with checked reads/writes for sum. Keel grows its
  unique array with `array.push`; this gives Haskell the benefit of knowing the final capacity.
- The Haskell tree stays shared across eight scans. Binary-trees retains its long-lived
  tree and builds/checks each short-lived tree separately. Keel uses its existing arenas;
  Haskell uses ordinary GC-managed algebraic data. These allocation strategies are not identical.
- `-fno-full-laziness -fno-cse` prevent GHC from hoisting repeated pure tree computations
  or sharing identical child constructions. They apply to the whole Haskell executable;
  this is explicitly not an unrestricted default `-O2` comparison.
- The pair in `churn` can be eliminated by GHC. That row measures the optimized program,
  and should not be interpreted as Haskell heap allocation throughput. Likewise Keel can
  reuse list cells whereas the Haskell map port builds new strict cells.
- Keel checks integer overflow; Haskell machine arithmetic wraps. None of these workloads
  overflow signed arithmetic; the RNG intentionally wraps in both versions.
- No compiler/runtime tuning sweep was performed. System load can change these timings;
  compare the freshly measured rows here rather than numbers from earlier comparison runs.

## Reproduce

From the repository root (macOS; requires GHC, Cabal, Python 3, and the native linker):

```sh
cd ref
cabal build keelc
cd ..
python3 ref/bench/haskell/compare.py
```

Use `--sizes small,medium,large` to include small Goose workloads or `--reps N` to
change the repetition count. The runner writes results after every completed workload;
it stops on a build error, nonzero exit, or checksum mismatch.
