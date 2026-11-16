"""Sequential, resumable Lean kernel check. Run with: lake env python3 check_proofs.py"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--memory-mib', type=int, default=6144)
    parser.add_argument('--plan-only', action='store_true', help='Validate the dependency order without running compilers')
    args = parser.parse_args()
    if args.memory_mib <= 0:
        parser.error('--memory-mib must be positive')
    root = Path(__file__).resolve().parent
    os.chdir(root)
    subprocess.run([sys.executable, 'verify_release.py'], check=True)
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    if '11acb17ec6b07a8f9e9173e6845197929540936b' not in version:
        raise SystemExit('Unexpected Lean compiler: ' + version)
    cache = root / '.lake/proof-check'
    cache.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['LEAN_PATH'] = str(cache) + os.pathsep + env.get('LEAN_PATH', '')
    order, visited, visiting = [], set(), set()
    fingerprints = {}

    def visit(name):
        if name in visited:
            return
        if name in visiting:
            raise SystemExit('Cyclic import: ' + name)
        visiting.add(name)
        text = (root / (name + '.lean')).read_text()
        deps = []
        for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
            for dep in line.split('--', 1)[0].split():
                if dep in manifest['modules']:
                    visit(dep)
                    deps.append(fingerprints[dep])
        fingerprint = hashlib.sha256((text + ''.join(deps)).encode()).hexdigest()
        if fingerprint != manifest['modules'][name]['dependency_fingerprint']:
            raise SystemExit('Dependency fingerprint mismatch: ' + name)
        fingerprints[name] = fingerprint
        visiting.remove(name)
        visited.add(name)
        order.append(name)

    for name in manifest['roots']:
        visit(name)
    if visited != set(manifest['modules']):
        raise SystemExit('Manifest includes modules outside the theorem closure')
    if args.plan_only:
        print('Dependency order and fingerprints match:', len(order), 'modules.')
        return
    for i, name in enumerate(order, 1):
        stamp = cache / (name + '.sha256')
        artifacts = [cache / (name + suffix) for suffix in ['.olean', '.olean.private', '.olean.server', '.log']]
        if stamp.exists() and stamp.read_text() == fingerprints[name] and all(p.is_file() for p in artifacts):
            continue
        stamp.unlink(missing_ok=True)
        print(f'[{i}/{len(order)}] {name}', flush=True)
        with (cache / (name + '.log')).open('w') as log:
            subprocess.run(['lean', '-j1', '-M' + str(args.memory_mib),
                            '-DwarningAsError=true', '-DmaxHeartbeats=0',
                            '-Dlinter.unreachableTactic=false', '-Dlinter.unusedTactic=false',
                            '-DElab.async=false', '-o', str(cache / (name + '.olean')),
                            name + '.lean'], env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        if not all(p.is_file() for p in artifacts):
            raise SystemExit('Missing compiler output: ' + name)
        stamp.write_text(fingerprints[name])
    combined = cache / 'endpoint-axioms.log'
    report_modules = {v['module'] for v in json.loads((root / 'verification/checked-endpoints.json').read_text())['named_reports'].values()}
    combined.write_text('\n'.join((cache / (n + '.log')).read_text() for n in sorted(report_modules)))
    subprocess.run([sys.executable, 'verify_release.py', '--axiom-log', str(combined)], check=True)
    print('Kernel check complete:', len(order), 'modules.')


if __name__ == '__main__':
    main()
