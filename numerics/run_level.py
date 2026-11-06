#!/usr/bin/env python3
"""Print, or explicitly run, one endpoint verification from the table."""
import argparse
import os
from pathlib import Path
import re
import signal
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent


def levels():
    return {int(n): (int(q), method, int(parameter))
            for line in (ROOT / 'data/levels.tsv').read_text().splitlines()
            if line.strip() and not line.startswith('#')
            for n, q, method, parameter in [line.split()]}


def command(n, *, workers=1, budget=8):
    q, method, p = levels()[n]
    if method == 'block_wiedemann':
        raise ValueError('N=97 uses the distributed pipeline: see n97/README.md')
    binaries = {
        'direct': 'spatial_qorder_f2_parity',
        'flint': 'exact_q_rank_flint',
        'prime_dense': 'spatial_crt_kernel_f2_parity_dense',
        'prime_core': 'spatial_crt_kernel_f2_parity_core',
        'composite_crt': 'spatial_crt_composite_f2_parity_parallel',
    }
    if method.startswith('two_prime'):
        args = ['spatial_crt_kernel_f2_twoprime', n, q // n, p,
                '--block-finish', '--sector-workers', workers,
                '--peak-budget-gib', budget, '--force']
        if method == 'two_prime_projected':
            args += ['--project-slack', 890013, 65536, 3]
    else:
        args = [binaries[method], n]
        if method == 'composite_crt':
            args += [p]
        args += [q]
        if method not in ('direct', 'flint'):
            args += ['--force']
    return [str(ROOT / 'bin' / args[0]), *map(str, args[1:])]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('N', type=int)
    parser.add_argument('--run', action='store_true', help='execute; default only prints the command')
    parser.add_argument('--threads', type=int, default=1)
    parser.add_argument('--sector-workers', type=int, default=1)
    parser.add_argument('--memory-gib', type=int, default=8, help='hard address-space limit; also two-prime peak-budget guard')
    parser.add_argument('--timeout', type=int, default=3600, help='wall-time limit in seconds')
    args = parser.parse_args()
    if min(args.threads, args.sector_workers, args.memory_gib, args.timeout) < 1:
        parser.error('resource limits must be positive')
    try:
        cmd = command(args.N, workers=args.sector_workers, budget=args.memory_gib)
    except (KeyError, ValueError) as exc:
        parser.error(str(exc))
    cmd = ['timeout', '--signal=TERM', '--kill-after=30s', str(args.timeout),
           'prlimit', '--as=' + str(args.memory_gib * 1024**3), '--', *cmd]
    env = dict(os.environ, OMP_NUM_THREADS=str(args.threads), OMP_DYNAMIC='false',
               OMP_MAX_ACTIVE_LEVELS='2', OMP_PROC_BIND='false')
    print('OMP_NUM_THREADS=' + str(args.threads), shlex.join(cmd), flush=True)
    if not args.run:
        return
    proc = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, start_new_session=True)
    certified = False
    try:
        for line in proc.stdout:
            print(line, end='', flush=True)
            certified |= bool(re.search(r'\b(?:full_defect|final_defect)=0\b', line))
        status = proc.wait()
    except BaseException:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
        raise
    if status or not certified:
        raise SystemExit(f'No spanning certificate: exit={status}, zero-defect marker={certified}')
    print(f'ENDPOINT_VERIFIED N={args.N}')


if __name__ == '__main__':
    main()
