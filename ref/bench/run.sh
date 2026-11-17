#!/bin/sh
# Build every benchmark with keelc (ARM64) and print the best of 5 wall-clock times.
cd "$(dirname "$0")" || exit 1
REF=$(cd .. && pwd)
K=$(cd "$REF" && cabal list-bin keelc)
OUT=${TMPDIR:-/tmp}/keel-bench
mkdir -p "$OUT"
export keel_ref_datadir="$REF"
for f in *.kl; do
  "$K" build "$f" -o "$OUT/${f%.kl}" > /dev/null || exit 1
done
(
  cd "$REF" || exit 1
  "$K" build selfhost/parse.kl -o "$OUT/parse" > /dev/null || exit 1
  "$K" build selfhost/core.kl -o "$OUT/selfcheck" > /dev/null || exit 1
  "$K" build selfhost/run.kl -o "$OUT/interp" > /dev/null || exit 1
  "$K" build selfhost/repl.kl -o "$OUT/repl" > /dev/null || exit 1
) || exit 1
python3 - "$OUT" "$REF" *.kl <<'PY'
import os, subprocess, sys, time
out, ref, files = sys.argv[1], sys.argv[2], sys.argv[3:]
env = dict(os.environ, keel_ref_datadir=ref)
for f in files:
    exe = f"{out}/{f[:-3]}"
    best, result = None, ""
    for _ in range(5):
        t = time.perf_counter()
        p = subprocess.run([exe], capture_output=True, text=True)
        dt = time.perf_counter() - t
        best = dt if best is None else min(best, dt)
        result = p.stdout.strip().splitlines()[-1]
    print(f"{f[:-3]:9} {best * 1000:8.1f} ms   {result}")

selfhost = [
    ("parse", f"{ref}/selfhost/checker.kl", True),
    ("selfcheck", "selfhost/core.kl\n", False),
    ("interp", "examples/fact.kl\n", False),
    ("repl", f"{ref}/bench/repl-session.in", True),
]
for name, inp, is_file in selfhost:
    exe = f"{out}/{name}"
    stdin_data = open(inp).read() if is_file else inp
    best, result = None, ""
    for _ in range(5):
        t = time.perf_counter()
        p = subprocess.run([exe], input=stdin_data, cwd=ref, env=env, capture_output=True, text=True)
        if p.returncode != 0:
            raise RuntimeError(f"{name} failed ({p.returncode}): {p.stderr}")
        dt = time.perf_counter() - t
        best = dt if best is None else min(best, dt)
        result = p.stdout.strip().splitlines()[-1]
    print(f"{name:9} {best * 1000:8.1f} ms   {result}")
PY
