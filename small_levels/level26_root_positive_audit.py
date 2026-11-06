"""Independent bounded regeneration of N26 pole and weight certificates.

Build outputs and compiler logs stay in /tmp. Each child is bounded and
runs sequentially; the original symbolic systems are regenerated, not just
the saved final polynomial ideals.
"""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import hashlib
import itertools
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
wide = json.loads((ROOT / 'level26_prime5_wide_certificate.json').read_text())
weights = json.loads((ROOT / 'level26_prime5_weightk_certificate.json').read_text())
small = json.loads((ROOT / 'level26_prime5_resume_data.json').read_text())
results = {}

def run(name, args, code, timeout=90):
    log = Path('/tmp/level26_root_audit_' + code + '_' + name + '.log')
    with log.open('w') as stream:
        subprocess.run([sys.executable, '-B', str(ROOT / (name + '.py')), *args],
                       stdout=stream, stderr=subprocess.STDOUT,
                       timeout=timeout, check=True)
    return hashlib.sha256(log.read_bytes()).hexdigest()

for letters in itertools.product('mp', repeat=3):
    code = ''.join(letters)
    signs = ['-1' if c == 'm' else '1' for c in code]
    checks = {}
    checks['wide_rows'] = run('level26_prime5_wide_first_jet', signs + ['grid780', 'probe'], code)
    actual = json.loads(Path('/tmp/level26_prime5_rows_780_' + code + '.json').read_text())
    assert actual == wide['cases'][code]['rows'], (code, 'wide rows differ')
    checks['continuation'] = run('level26_prime5_wide_continuation', signs + ['grid780'], code)
    actual = json.loads(Path('/tmp/level26_prime5_wide_continuation_' + code + '.json').read_text())
    assert actual == wide['cases'][code]['continuation'], (code, 'continuation differs')
    checks['weight_polynomials'] = run('level26_prime5_weightk_eliminate', [code, 'magma'], code)
    actual = json.loads(Path('/tmp/level26_prime5_weightk_polys_' + code + '.json').read_text())
    assert actual == weights['cases'][code]['original_polynomials'], (code, 'weight polynomials differ')
    checks['weight_two'] = run('level26_prime5_weightk_probe', [code, '1'], code)
    actual = json.loads(Path('/tmp/level26_prime5_weightk_' + code + '_1.json').read_text())
    assert actual['chart_bases'] == [['1'], ['1']], code
    if letters[-1] == 'p':
        checks['small_rows'] = run('level26_prime5_first_jet', signs + ['grid390', 'probe'], code)
        checks['positive_rank'] = run('level26_prime5_rank', [code], code)
    results[code] = checks
    print(code, 'fresh source regeneration PASS', flush=True)

names = set(wide['source_sha256']) | set(weights['source_sha256'])
names.update(['level26_modularity_agent_complete.tex',
              'level26_modularity_agent_complete.py',
              'level26_modularity_agent_generation.py',
              'level25_finish_dilation_mellin.tex'])
manifest = {'claim': 'All8 fresh Q780 continuation and leading rows; all8 original weight polynomials and weight2 ideals; positive13 first-source rank.',
            'cases': results,
            'source_sha256': {name: source_sha256(ROOT/name) for name in sorted(names)}}
manifest['document_hash_provenance'] = recorded_document_provenance(); (ROOT/'level26_root_positive_audit.json').write_text(json.dumps(manifest, indent=2)+'\n')
print('N26_ROOT_POSITIVE_SOURCE_AUDIT_PASS', flush=True)
