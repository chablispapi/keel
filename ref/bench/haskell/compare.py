#!/usr/bin/env python3
"""Build and compare all existing Keel workloads with strict Haskell ports."""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
REF = HERE.parents[1]

def run(cmd, **kw):
    p = subprocess.run(list(map(str, cmd)), capture_output=True, text=True, **kw)
    if p.returncode:
        raise RuntimeError(f'{cmd}\n{p.stdout}{p.stderr}')
    return p.stdout.strip()

def measure(cmd):
    start = time.perf_counter()
    p = subprocess.run(['/usr/bin/time', '-l', *map(str, cmd)],
                       capture_output=True, text=True, check=True)
    ms = (time.perf_counter() - start) * 1000
    rss = int(re.search(r'(\d+)\s+maximum resident set size', p.stderr)[1]) / 2**20
    out = p.stdout.strip()
    if out.startswith('result:'):
        out = out.split(':', 1)[1].strip()
    else:
        out = '\n'.join(x for x in out.splitlines() if not x.startswith('result:'))
    return {'ms': ms, 'mb': rss, 'output': out}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reps', type=int, default=5)
    ap.add_argument('--sizes', default='medium,large')
    ap.add_argument('--output', type=Path, default=HERE / 'results.json')
    args = ap.parse_args()
    if args.reps < 1:
        ap.error('--reps must be positive')
    keelc = run(['cabal', 'list-bin', 'keelc'], cwd=REF)
    env = dict(os.environ, keel_ref_datadir=str(REF))
    env.pop('KEEL_STATS', None)
    env.pop('GHCRTS', None)
    flags = ['-O2', '-XFlexibleContexts', '-fno-full-laziness', '-fno-cse']
    result = {'ghc': run(['ghc', '--version']), 'platform': platform.platform(),
              'keel_commit': run(['git', 'rev-parse', 'HEAD'], cwd=REF),
              'flags': flags, 'reps': args.reps, 'rows': []}
    jobs = [(name, n, REF/'bench'/f'{name}.kl', None) for name, n in
            [('loop',200000000), ('sort',3000), ('churn',10000000), ('map',1000), ('fib',32)]]
    sizes = {'small': (1000000,16,15), 'medium': (16000000,20,17),
             'large': (128000000,24,19)}
    for size in args.sizes.split(','):
        for name,n in zip(('sum','tree','bintrees'), sizes[size]):
            jobs.append((name,n,REF/'bench/goose'/f'{name}.kl',size))
    with tempfile.TemporaryDirectory(prefix='keel-haskell-') as temp:
        work = Path(temp)
        run(['ghc', *flags, '-outputdir', work, HERE/'Main.hs', '-o', work/'haskell'])
        (work/'rng.kl').write_text((REF/'bench/goose/rng.kl').read_text())
        for name,n,source,size in jobs:
            src = source.read_text()
            if size:
                src = re.sub(r'\b\d+(\s*-- BENCH_N)', lambda m: str(n)+m[1], src)
            kl = work/f'{name}.kl'
            kl.write_text(src)
            run([keelc,'build',kl,'-o',work/'keel'], env=env)
            commands = {'keel':[work/'keel'], 'haskell':[work/'haskell',name,str(n)]}
            samples = {lang:[] for lang in commands}
            expected = None
            # Warm both binaries, then alternate execution order each repetition.
            for lang,cmd in commands.items():
                sample = measure(cmd)
                if expected is None:
                    expected = sample['output']
                if sample['output'] != expected:
                    raise RuntimeError(f'{name} {n}: checksum mismatch: {sample} vs {expected}')
            for rep in range(args.reps):
                for lang in (list(commands) if rep % 2 == 0 else list(reversed(commands))):
                    sample = measure(commands[lang])
                    if sample['output'] != expected:
                        raise RuntimeError(f'{name} {n}: unstable checksum')
                    samples[lang].append(sample)
            row = {'name':name, 'n':n, 'size':size, 'output':expected, 'samples':samples}
            result['rows'].append(row)
            parts = [f'{lang}: {min(s["ms"] for s in ss):.1f} ms / '
                     f'{max(s["mb"] for s in ss):.1f} MB' for lang,ss in samples.items()]
            print(f'{name} {n}: ' + '; '.join(parts), flush=True)
            args.output.write_text(json.dumps(result, indent=2)+'\n')

if __name__ == '__main__':
    main()
