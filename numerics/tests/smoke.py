#!/usr/bin/env python3
"""Bounded exact regression checks; never launches a production level."""
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ENV = dict(os.environ, OMP_NUM_THREADS='2', OMP_DYNAMIC='false', OMP_MAX_ACTIVE_LEVELS='2')

levels = {int(n): int(q) for line in (ROOT / 'data/levels.tsv').read_text().splitlines()
          if line.strip() and not line.startswith('#')
          for n, q, _, _ in [line.split()]}
expected = {n for n in range(1, 96) if n % 16 and all(n % (p*p) for p in (3, 5, 7))}
assert set(levels) == expected | {97}
minima = {int(n): int(q) for line in (ROOT / 'data/minimality.tsv').read_text().splitlines()
          if line.strip() and not line.startswith('#') for n, q in [line.split()]}
assert minima == {n: q for n, q in levels.items() if n <= 95}
print('PASS complete admissible-level and minimality manifests')


def run(binary, *args):
    cmd = ['timeout', '--kill-after=5s', '120', 'prlimit', '--as=2147483648', '--', str(ROOT / 'bin' / binary), *map(str, args)]
    result = subprocess.run(cmd, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        raise AssertionError(result.stdout)
    return result.stdout


def require(text, pattern):
    if not re.search(pattern, text):
        raise AssertionError(f'Missing {pattern!r}:\n{text}')


for binary, args in [
    ('spatial_qorder_f2_parity', (5, 6)),
    ('spatial_crt_kernel_f2_parity_dense', (11, 44)),
    ('spatial_crt_kernel_f2_parity_core', (11, 44)),
    ('spatial_crt_composite_f2_parity_parallel', (22, 11, 132)),
    ('spatial_crt_kernel_f2_twoprime', (17, 24, 3, '--block-finish', '--sector-workers', 2)),
    ('exact_q_rank_flint', (38, 1596)),
]:
    output = run(binary, *args)
    require(output, r'\b(?:full_defect|final_defect)=0\b')
    print('PASS', binary, *args)

for n, q in [(5, 6), (38, 1596)]:
    output = run('spatial_qorder_hall_screen_general_u64', '--minimal', n, q)
    require(output, 'NO_EARLIER_FULL_RANK')
    require(output, r'PIPELINE_SUMMARY .*status=PASS')
    print('PASS minimality', n, q)

output = run('spatial_qorder_f2_parity', 38, 1596)
require(output, r'\bfull_defect=2\b')
print('PASS N=38 characteristic-two rank drop')

output = run('spatial_crt_bw_export', 97, 5942336400, 0, '--estimate')
for field in ['rows=30686496', 'columns=30630600', 'nonzeros=1474426612']:
    require(output, field + r'\b')
output = run('spatial_qorder_hall_screen', 97, 5942336400)
require(output, r'\bstatus=PASS_SCREEN\b')
output = run('spatial_crt_kernel_f2_bw_finish_minor_largeq', 97, 5942336400, '--setup-only')
require(output, 'LARGE_Q_SETUP_PASS')
print('PASS N=97 dimensions and 64-bit setup (no matrix allocation)')
print('SMOKE_PASS')
