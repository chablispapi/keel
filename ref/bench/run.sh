#!/bin/sh
# Build every benchmark with keelc (ARM64) and print the best of 5 wall-clock times.
cd "$(dirname "$0")" || exit 1
K=$(cd .. && cabal list-bin keelc)
OUT=${TMPDIR:-/tmp}/keel-bench
mkdir -p "$OUT"
for f in *.kl; do
  "$K" build "$f" -o "$OUT/${f%.kl}" > /dev/null || exit 1
done
python3 - "$OUT" *.kl <<'PY'
import subprocess, sys, time
out, files = sys.argv[1], sys.argv[2:]
for f in files:
    exe = f"{out}/{f[:-3]}"
    best, result = None, ""
    for _ in range(5):
        t = time.perf_counter()
        p = subprocess.run([exe], capture_output=True, text=True)
        dt = time.perf_counter() - t
        best = dt if best is None else min(best, dt)
        result = p.stdout.strip().splitlines()[-1]
    print(f"{f[:-3]:6} {best * 1000:8.1f} ms   {result}")
PY
