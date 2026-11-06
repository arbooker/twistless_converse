"""Check an assembled source manifest and optional release-endpoint axiom log.

This is not a substitute for Lean compilation. See BUILD.txt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--axiom-log', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    problems = []
    for name, record in manifest['modules'].items():
        p = root / (name + '.lean')
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != record['source_sha256']:
            problems.append('Source mismatch: ' + name)
    expected = set(manifest['modules']) | {'ReleaseCheck'}
    actual = {p.stem for p in root.glob('*.lean')}
    if expected != actual:
        problems.append('Unexpected/missing Lean files: ' + str(sorted(expected ^ actual)))
    for name, digest in manifest['package_support_sha256'].items():
        p = root / name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != digest:
            problems.append('Package support mismatch: ' + name)
    for name, digest in manifest.get('release_artifacts_sha256', {}).items():
        p = root.parent / name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != digest:
            problems.append('Release artifact mismatch: ' + name)
    if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc2':
        problems.append('Unexpected Lean toolchain')
    packages = json.loads((root / 'lake-manifest.json').read_text())['packages']
    mathlib = [p for p in packages if p['name'] == 'mathlib']
    if len(mathlib) != 1 or mathlib[0]['rev'] != '065356127b1dc0016f66b7283ce0ce2c4055aa55':
        problems.append('Unexpected Mathlib revision')
    if args.axiom_log:
        log = args.axiom_log.read_text()
        if 'sorryAx' in log or re.search(r'(?im)^.*\berror:', log):
            problems.append('Compiler error or sorryAx in log')
        reports = {}
        for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log):
            values = {a.strip() for a in axioms.split(',') if a.strip()}
            if not values <= {'propext', 'Classical.choice', 'Quot.sound'}:
                problems.append('Nonstandard axioms: ' + name + ': ' + str(values))
            reports[name] = values
        for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
            reports[name] = set()
        required = {d for ds in manifest['roots'].values() for d in ds}
        if not required <= set(reports):
            problems.append('Missing endpoint axiom reports: ' + str(sorted(required - set(reports))))
    if problems:
        raise SystemExit('\n'.join(problems))
    print('Source bytes and pins match:', len(manifest['modules']), 'modules.')
    if args.axiom_log:
        print('All named endpoint axiom reports are present and standard-only.')


if __name__ == '__main__':
    main()
