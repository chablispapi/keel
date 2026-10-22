#!/usr/bin/env python3
"""Run Keel's ports of three Goose benchmarks next to Goose's own, C++ and Rust versions on
this machine: same sizes, same checksums (the harness stops if any row disagrees).

  python3 bench/goose/compare.py GOOSE_CHECKOUT [--sizes small,medium,large] [--reps 3]
                                 [--host USER@MACHINE]

GOOSE_CHECKOUT is a clone of github.com/aardappel/goose with the compiler built at
build/goose (cmake -S . -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build).
Times are the best of --reps whole-process wall clocks; memory is the peak RSS.

With --host, everything runs on that x86-64 Linux machine (over ssh; it needs gcc, g++,
rustc and python3): Keel through its x86_64 back end, Goose's C output with gcc -O2, the C++
with g++ -O2. Goose itself still runs here, to produce that C.
"""
import argparse, json, os, re, shlex, subprocess, sys, tempfile, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REF = HERE.parent.parent

# name: (sizes, keel file, goose rows, cpp rows (label, variant), rust rows)
BENCHES = {
    "sum": ([1000000, 16000000, 128000000], "sum.kl", ["sum.goose"],
            [("cpp vector", 0), ("cpp vector+reserve", 1)], ["sum.rs"]),
    "tree": ([16, 20, 24], "tree.kl", ["tree.goose"],
             [("cpp unique_ptr", 0), ("cpp new/delete", 1), ("cpp arena", 2)],
             ["tree_box.rs", "tree_arena.rs"]),
    "bintrees": ([15, 17, 19], "bintrees.kl", ["bintrees.goose"],
                 [("cpp new/delete", 0), ("cpp arena", 1)],
                 ["bintrees_box.rs", "bintrees_arena.rs"]),
}
SIZES = ["small", "medium", "large"]


def with_n(src, n):
    """The source with the number on its `BENCH_N` line replaced by n."""
    return re.sub(r"\b\d[\d_]*(\s*;?\s*(?://|--) BENCH_N)", lambda m: f"{n}{m.group(1)}", src, count=1)


def sh(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.exit(f"failed: {' '.join(map(str, cmd))}\n{r.stdout}{r.stderr}")
    return r.stdout


def measure(exe, reps):
    """Best wall clock (ms), peak RSS (MB) and stdout without keelc's result line."""
    best, rss, out = None, 0, ""
    for _ in range(reps):
        t = time.perf_counter()
        r = subprocess.run(["/usr/bin/time", "-l", exe], capture_output=True, text=True)
        dt = (time.perf_counter() - t) * 1000
        if r.returncode != 0:
            return None, None, f"exit {r.returncode}: {r.stderr.strip()[-200:]}"
        best = dt if best is None else min(best, dt)
        m = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
        rss = max(rss, int(m.group(1)) / 2**20 if m else 0)
        out = "\n".join(l for l in r.stdout.splitlines() if not l.startswith("result:"))
    return best, rss, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("goose", type=Path)
    ap.add_argument("--sizes", default="small,medium")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--only", default=",".join(BENCHES))
    ap.add_argument("--keel-only", action="store_true", help="skip the Goose, C++ and Rust rows")
    ap.add_argument("--host", help="run on this x86-64 Linux machine (ssh destination)")
    args = ap.parse_args()
    if args.host:
        return remote(args)
    gb = args.goose / "bench"
    keelc = sh(["cabal", "list-bin", "keelc"], cwd=REF).strip()
    env = dict(os.environ, keel_ref_datadir=str(REF))
    work = Path(tempfile.mkdtemp(prefix="keel-vs-goose-"))
    (work / "rng.goose").write_text((gb / "goose/rng.goose").read_text())
    (work / "rng.kl").write_text((HERE / "rng.kl").read_text())
    (work / "bench.rs").write_text((gb / "rust/bench.rs").read_text())

    for name in args.only.split(","):
        sizes, kl, gooses, cpps, rusts = BENCHES[name]
        for sname in args.sizes.split(","):
            n = sizes[SIZES.index(sname)]
            rows = []  # (label, exe)
            src = work / f"{name}_{n}.kl"
            src.write_text(with_n((HERE / kl).read_text(), n))
            sh([keelc, "build", src, "-o", work / f"keel_{name}"], env=env)
            rows.append(("keel", work / f"keel_{name}"))
            for g in [] if args.keel_only else gooses:
                gs, c = work / g, work / f"{g}.c"
                gs.write_text(with_n((gb / "goose" / g).read_text(), n))
                sh([args.goose / "build/goose", "-O2", "--standalone", "-o", c, gs])
                sh(["clang", "-O2", "-w", "-DGS_STACK_RESERVE=2147483648ull", c, "-o", work / g[:-6]])
                rows.append(("goose", work / g[:-6]))
            for label, v in [] if args.keel_only else cpps:
                exe = work / f"{name}_cpp{v}"
                sh(["clang++", "-O2", "-std=c++20", f"-DBENCH_N={n}", f"-DVARIANT={v}",
                    f"-I{gb / 'cpp'}", gb / "cpp" / f"{name}.cpp", "-o", exe])
                rows.append((label, exe))
            for r in [] if args.keel_only else rusts:
                rs = work / r
                rs.write_text(with_n((gb / "rust" / r).read_text(), n))
                sh(["rustc", "-O", "-C", "codegen-units=1", rs, "-o", work / r[:-3]], cwd=work)
                rows.append(("rust " + r[:-3].split("_")[-1] if "_" in r else "rust", work / r[:-3]))

            print(f"\n{name} {sname} (N={n})")
            expected = None
            for label, exe in rows:
                ms, mb, out = measure(exe, args.reps)
                if ms is None:
                    print(f"  {label:22} {out}")
                    continue
                expected = expected or out
                ok = "" if out == expected else f"   CHECKSUM DIFFERS: {out.split()}"
                print(f"  {label:22} {ms:9.1f} ms {mb:9.1f} MB{ok}")


# Runs on the remote machine: build each job, then time it; prints one JSON object per job.
RUNNER = r"""
import json, os, subprocess, sys, time
os.chdir(os.path.dirname(os.path.abspath(__file__)))
reps = int(sys.argv[1])
for job in json.load(open("jobs.json")):
    b = subprocess.run(job["build"], shell=True, capture_output=True, text=True)
    if b.returncode:
        print(json.dumps({**job, "error": "build: " + b.stderr[-300:]}), flush=True)
        continue
    best, rss, out, err = None, 0, "", ""
    for _ in range(reps):
        t = time.perf_counter()
        p = subprocess.Popen(["./" + job["exe"]], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        o, e = p.stdout.read(), p.stderr.read()
        _, status, ru = os.wait4(p.pid, 0)  # this child's own peak RSS
        dt = (time.perf_counter() - t) * 1000
        code = os.waitstatus_to_exitcode(status)
        if code:
            err = "exit %d: %s" % (code, e[-200:])
            break
        best = dt if best is None else min(best, dt)
        rss = max(rss, ru.ru_maxrss / 1024)
        out = "\n".join(l for l in o.splitlines() if not l.startswith("result:"))
    print(json.dumps({**job, "ms": best, "mb": rss, "out": out, "error": err}), flush=True)
"""


def remote(args):
    """Prepare every program here, then build and run them all on args.host."""
    gb = args.goose / "bench"
    keelc = sh(["cabal", "list-bin", "keelc"], cwd=REF).strip()
    env = dict(os.environ, keel_ref_datadir=str(REF))
    work = Path(tempfile.mkdtemp(prefix="keel-vs-goose-x86-"))
    (work / "rng.goose").write_text((gb / "goose/rng.goose").read_text())
    (work / "rng.kl").write_text((HERE / "rng.kl").read_text())
    (work / "bench.rs").write_text((gb / "rust/bench.rs").read_text())
    sh(["cp", "-r", gb / "cpp", work / "cpp"])
    jobs = []
    for name in args.only.split(","):
        sizes, kl, gooses, cpps, rusts = BENCHES[name]
        for sname in args.sizes.split(","):
            n = sizes[SIZES.index(sname)]
            row = lambda label, build, exe: jobs.append({"bench": name, "size": sname, "n": n, "label": label, "build": build, "exe": exe})
            src = work / f"{name}_{n}.kl"
            src.write_text(with_n((HERE / kl).read_text(), n))
            exe = f"keel_{name}_{n}"
            sh([keelc, "build", src, "--target", "x86_64", "-o", work / exe], env=env)
            row("keel", f"gcc -no-pie -o {exe} {exe}.s", exe)
            if args.keel_only:
                continue
            for g in gooses:
                gs, exe = work / f"{n}_{g}", f"goose_{name}_{n}"
                gs.write_text(with_n((gb / "goose" / g).read_text(), n))
                sh([args.goose / "build/goose", "-O2", "--standalone", "-o", work / f"{exe}.c", gs])
                row("goose", f"gcc -O2 -w -DGS_STACK_RESERVE=2147483648ull {exe}.c -o {exe}", exe)
            for label, v in cpps:
                exe = f"cpp_{name}_{n}_{v}"
                row(label, f"g++ -O2 -std=c++20 -DBENCH_N={n} -DVARIANT={v} -Icpp cpp/{name}.cpp -o {exe}", exe)
            for r in rusts:
                exe = f"rust_{r[:-3]}_{n}"
                (work / f"{exe}.rs").write_text(with_n((gb / "rust" / r).read_text(), n))
                row("rust " + r[:-3].split("_")[-1] if "_" in r else "rust", f"rustc -O -C codegen-units=1 {exe}.rs -o {exe}", exe)
    (work / "jobs.json").write_text(json.dumps(jobs))
    (work / "runner.py").write_text(RUNNER)
    there = "/tmp/keel-vs-goose"
    sh(["ssh", args.host, f"rm -rf {there}"])
    sh(["scp", "-q", "-r", work, f"{args.host}:{there}"])
    proc = subprocess.Popen(["ssh", args.host, f"python3 {there}/runner.py {args.reps}"], stdout=subprocess.PIPE, text=True)
    expected, current = {}, None
    for l in proc.stdout:
        r = json.loads(l)
        key = (r["bench"], r["size"])
        if key != current:
            current = key
            print(f"\n{r['bench']} {r['size']} (N={r['n']}) on {args.host}")
        if r["error"]:
            print(f"  {r['label']:22} {r['error']}")
            continue
        expected.setdefault(key, r["out"])
        ok = "" if r["out"] == expected[key] else f"   CHECKSUM DIFFERS: {r['out'].split()}"
        print(f"  {r['label']:22} {r['ms']:9.1f} ms {r['mb']:9.1f} MB{ok}", flush=True)
    proc.wait()


if __name__ == "__main__":
    main()
