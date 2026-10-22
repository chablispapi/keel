#!/usr/bin/env python3
"""Compare AArch64 full-field reuse against its generic-helper baseline (macOS)."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import tempfile
import time

REF = Path(__file__).resolve().parents[1]


def run(command, **kwargs):
    result = subprocess.run(list(map(str, command)), capture_output=True, text=True, **kwargs)
    if result.returncode:
        raise RuntimeError(f'{command}: exit {result.returncode}\n{result.stdout}{result.stderr}')
    return result


def measure(exe, environment):
    start = time.perf_counter()
    result = run(['/usr/bin/time', '-l', exe], env=environment)
    elapsed = (time.perf_counter() - start) * 1000
    rss = int(re.search(r'(\d+)\s+maximum resident set size', result.stderr)[1])
    return {'ms': elapsed, 'rss_bytes': rss, 'output': result.stdout}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reps', type=int, default=15)
    parser.add_argument('--sizes', default='medium,large')
    parser.add_argument('--only', help='Comma-separated workload names for focused reruns')
    parser.add_argument('--output', type=Path, default=Path('/tmp/keel-reuse-results.json'))
    args = parser.parse_args()
    if platform.system() != 'Darwin' or platform.machine() != 'arm64':
        parser.error('requires an AArch64 macOS host')
    sizes = {'small': (1000000, 16, 15), 'medium': (16000000, 20, 17),
             'large': (128000000, 24, 19)}
    if args.reps < 3 or any(size not in sizes for size in args.sizes.split(',')):
        parser.error('use at least three repetitions and small,medium,large sizes')
    jobs = [(name, None, REF/'bench'/f'{name}.kl', None) for name in
            ['loop', 'sort', 'churn', 'map', 'fib']]
    jobs += [(name, size, REF/'bench/goose'/f'{name}.kl', n)
             for size in args.sizes.split(',')
             for name, n in zip(['sum', 'tree', 'bintrees'], sizes[size])]
    if args.only:
        chosen = args.only.split(',')
        if any(name not in [job[0] for job in jobs] for name in chosen):
            parser.error('unknown workload in --only')
        jobs = [job for job in jobs if job[0] in chosen]
    environment = dict(os.environ, keel_ref_datadir=str(REF))
    environment.pop('KEEL_STATS', None)
    diff = run(['git', 'diff', '--', 'ref/src/Keel/AArch64.hs'], cwd=REF.parent).stdout
    report = {'date_utc': datetime.now(timezone.utc).isoformat(),
              'revision': run(['git', 'rev-parse', 'HEAD'], cwd=REF).stdout.strip(),
              'aarch64_diff_sha256': hashlib.sha256(diff.encode()).hexdigest(),
              'platform': platform.platform(),
              'ghc': run(['ghc', '--version']).stdout.strip(),
              'reps': args.reps, 'rows': []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='keel-reuse-') as temp:
        work = Path(temp)
        emitter = work/'emit'
        run(['cabal', 'exec', '--', 'ghc', '-package', 'keel-ref', '-outputdir', work,
             REF/'bench/Reuse.hs', '-o', emitter], cwd=REF)
        (work/'rng.kl').write_text((REF/'bench/goose/rng.kl').read_text())
        for name, size, original, n in jobs:
            key = name if size is None else f'{name}-{size}'
            source = work/f'{key}.kl'
            text = original.read_text()
            if n is not None:
                text = re.sub(r'\b\d+(\s*-- BENCH_N)', lambda match: str(n) + match[1], text)
            source.write_text(text)
            run([emitter, source, work/key], env=environment)
            binaries, metrics, samples, counters = {}, {}, {}, {}
            for variant in ['baseline', 'candidate']:
                asm, exe = work/f'{key}.{variant}.s', work/f'{key}.{variant}'
                start = time.perf_counter()
                run(['cc', '-o', exe, asm])
                link_ms = (time.perf_counter()-start)*1000
                assembly = asm.read_text()
                size_text = run(['size', '-m', exe]).stdout
                text_bytes = int(re.search(r'Section __text:\s+(\d+)', size_text)[1])
                # Only user functions; exclude the entry point, printers and runtime.
                functions = assembly.split('\t.globl _main')[0]
                metrics[variant] = {'assembly_bytes': asm.stat().st_size,
                                    'binary_bytes': exe.stat().st_size,
                                    'text_bytes': text_bytes,
                                    'assemble_link_ms': link_ms,
                                    'reuse_calls': functions.count('bl _keel_drop_reuse'),
                                    'unique_guards': functions.count('lsr w10, w9, #10')}
                stats = run([exe], env=dict(environment, KEEL_STATS='1'))
                counters[variant] = dict((key, int(value)) for key, value in
                                         re.findall(r'(allocs|recycled|inplace|freed|live)=(\d+)', stats.stderr))
                if set(counters[variant]) != {'allocs', 'recycled', 'inplace', 'freed', 'live'}:
                    raise RuntimeError(f'{key}: missing allocator counters')
                binaries[variant] = exe
                samples[variant] = []
            if counters['baseline'] != counters['candidate'] or counters['candidate']['live'] != 0:
                raise RuntimeError(f'{key}: allocator counters differ or leak: {counters}')
            warmups = [run([exe], env=environment).stdout for exe in binaries.values()]
            if warmups[0] != warmups[1]:
                raise RuntimeError(f'{key}: warmup output mismatch')
            for rep in range(args.reps):
                order = list(binaries) if rep % 2 == 0 else list(reversed(binaries))
                for variant in order:
                    sample = measure(binaries[variant], environment)
                    if sample.pop('output') != warmups[0]:
                        raise RuntimeError(f'{key}: timed output mismatch')
                    samples[variant].append(sample)
            medians = {variant: statistics.median(s['ms'] for s in ss)
                       for variant, ss in samples.items()}
            row = {'name': key, 'n': n, 'output': warmups[0], 'metrics': metrics,
                   'counters': counters, 'samples': samples, 'median_ms': medians,
                   'peak_rss_bytes': {v: max(s['rss_bytes'] for s in ss) for v, ss in samples.items()},
                   'speedup': medians['baseline']/medians['candidate']}
            report['rows'].append(row)
            args.output.write_text(json.dumps(report, indent=2) + '\n')
            print(f'{key}: {medians["baseline"]:.2f} -> {medians["candidate"]:.2f} ms '
                  f'({row["speedup"]:.3f}x), identical counters', flush=True)


if __name__ == '__main__':
    main()
