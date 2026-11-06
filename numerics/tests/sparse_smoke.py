#!/usr/bin/env python3
"""Optional tiny end-to-end CADO certificate test (N=31, Q=10416)."""
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BWC = Path(os.environ['CADO_BWC_DIR']).resolve()
ENV = dict(os.environ, OMP_NUM_THREADS='2')


def run(program, *args):
    result = subprocess.run(
        ['timeout', '--kill-after=5s', '120', 'prlimit', '--as=2147483648', '--', str(program), *map(str,args)],
        env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


with tempfile.TemporaryDirectory(prefix='finiteness-sparse-smoke-') as tmp:
    work = Path(tmp)
    core = work / 'core.bin'
    square = work / 'square.bin'
    wdir = work / 'wdir'
    wdir.mkdir()
    print(run(ROOT/'bin/spatial_crt_bw_export', 31, 10416, 0, core), end='')
    print(run(ROOT/'bin/cado_square_complete_f2', core, 31001, square), end='')
    common = ['nullspace=RIGHT', 'n=64', 'm=64', 'prime=2', 'thr=1x2',
              'interval=64', 'seed=31005', 'lingen_thr=1x2',
              'balancing_options=reorder=columns', f'matrix={square}', f'wdir={wdir}']
    for stage in ['prep', 'secure', 'krylov', 'lingen', 'mksol', 'gather', 'cleanup']:
        run(BWC/'bwc.pl', stage, *common)
        print('PASS CADO', stage, flush=True)
    rank_report = run(ROOT/'bin/cado_rank_from_lingen_f2', 64, wdir/'F', '--max-order', 32, '--max-mib', 256)
    degree = int(re.search(r'^determinant_degree=(\d+)$',rank_report,re.M)[1])
    solution = wdir/'W.sols0-64'
    report = run(ROOT/'bin/cado_solution_check_f2', square, solution)
    print(report, end='')
    rank = int(re.search(r'\bcandidate_rank=(\d+)\b',report)[1])
    assert re.search(r'\bbad_rows=0\b',report)
    rows = square.with_suffix('.rw.bin').stat().st_size // 4
    assert degree + rank == rows, (degree,rank,rows)
    print(f'PASS complete square-kernel certificate: {degree}+{rank}={rows}')
    report = run(ROOT/'bin/spatial_crt_kernel_f2_bw_finish_minor_largeq',
                 31, 10416, core, 310013, 2, 3, solution)
    assert re.search(r'^PROJECTION_CERTIFIED .*final_defect=0 ',report,re.M), report
    print(report, end='')
print('SPARSE_SMOKE_PASS')
