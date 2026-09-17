#!/usr/bin/env python3
"""Compile every proof module, audit theorem closures and replay local declarations."""
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
os.environ['LEAN_NUM_THREADS'] = '1'
EVIDENCE = ROOT / 'evidence-complete'
EVIDENCE.mkdir(exist_ok=True)

def run(args, log):
    with (EVIDENCE / log).open('w') as out:
        result = subprocess.run(args, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        print((EVIDENCE / log).read_text()[-12000:], flush=True)
        raise SystemExit('Failed: ' + ' '.join(args))
    print('Passed: ' + ' '.join(args), flush=True)

run([sys.executable, 'scripts/bootstrap.py'], 'bootstrap.log')
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    actual = subprocess.check_output(['git', '-C', '.lake/packages/' + package['name'],
                                      'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit('Dependency revision mismatch: ' + package['name'])
print('Passed: all dependency revision checks', flush=True)

sources = {p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.'): p
           for p in (ROOT / 'ErdosProblems').rglob('*.lean')}
for name in ['JSP000393', 'JSP000393Complete', 'AuditComplete']:
    sources[name] = ROOT / (name + '.lean')
ordered = []
visiting = set()

def visit(name):
    if name in ordered:
        return
    if name in visiting:
        raise SystemExit('Cyclic import: ' + name)
    visiting.add(name)
    for dep in re.findall(r'^import\s+(\S+)', sources[name].read_text(), re.M):
        if dep in sources:
            visit(dep)
    visiting.remove(name)
    ordered.append(name)

for name in sources:
    visit(name)
for name in ordered:
    rel = sources[name].relative_to(ROOT).as_posix()
    olean = Path('.lake/build/lib/lean') / (name.replace('.', '/') + '.olean')
    olean.parent.mkdir(parents=True, exist_ok=True)
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '-j1', '-M10000',
         '-o', str(olean), './' + rel], 'build-' + name + '.log')

audit = (EVIDENCE / 'build-AuditComplete.log').read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit, re.S)
if len(reports) != 13:
    raise SystemExit('Expected exactly 13 axiom reports, got ' + str(len(reports)))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in reports:
    actual = {x.strip() for x in axioms.split(',') if x.strip()}
    if not actual <= allowed:
        raise SystemExit('Unexpected axiom in ' + name + ': ' + str(actual))
print('Passed: 13 strict axiom-closure audits', flush=True)

for module in ['ErdosProblems.Erdos485', 'JSP000393', 'JSP000393Complete']:
    run(['lake', 'env', 'leanchecker', '--verbose', module], 'kernel-' + module + '.log')

negative = EVIDENCE / 'Negative.lean'
negative.write_text('import Mathlib\nexample : (1 : Nat) = 0 := by decide\n')
result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(negative)],
                        capture_output=True, text=True)
(EVIDENCE / 'negative-control.log').write_text(result.stdout + result.stderr)
if result.returncode == 0 or 'error:' not in result.stdout + result.stderr:
    raise SystemExit('False-arithmetic control was not rejected as expected')
negative.unlink()
print('Passed: false-arithmetic negative control', flush=True)
record = {
    'status': 'passed',
    'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
    'preparation_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'modules_compiled': ordered,
    'axiom_reports': len(reports),
    'allowed_axioms': sorted(allowed),
    'dependency_count': len(manifest['packages']),
    'kernel_prefixes': ['ErdosProblems.Erdos485', 'JSP000393', 'JSP000393Complete'],
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sources.values()},
    'limits': 'Contributor-run replay with cached pinned Mathlib; no independent human certification.'
}
(EVIDENCE / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
