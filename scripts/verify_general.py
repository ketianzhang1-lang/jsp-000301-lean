#!/usr/bin/env python3
"""Freshly verify the original complete package and the coefficient-field extension."""
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
EVIDENCE = ROOT / 'evidence-general'
EVIDENCE.mkdir(exist_ok=True)

def run(args, log):
    with (EVIDENCE / log).open('w') as out:
        result = subprocess.run(args, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        print((EVIDENCE / log).read_text()[-12000:], flush=True)
        raise SystemExit('Failed: ' + ' '.join(args))
    print('Passed: ' + ' '.join(args), flush=True)

# The unchanged verifier rebuilds all 22 pinned upstream modules, two original
# proof modules, and AuditComplete, then checks the original 13 axiom closures.
run([sys.executable, 'scripts/verify_complete.py'], 'original-complete.log')
original = json.loads((ROOT / 'evidence-complete/verification.json').read_text())

for name in ['JSP000393General', 'AuditGeneral']:
    olean = Path('.lake/build/lib/lean') / (name + '.olean')
    olean.parent.mkdir(parents=True, exist_ok=True)
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '-j1', '-M10000',
         '-o', str(olean), name + '.lean'], 'build-' + name + '.log')

audit = (EVIDENCE / 'build-AuditGeneral.log').read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit, re.S)
expected = {
    'JSP000393General.' + x for x in [
        'schinzel_support_bound', 'schinzel_term_bound', 'uniform_threshold',
        'minimum_attained', 'minimum_le', 'minimum_diverges', 'family_counts',
        'minimum_family_upper_bound', 'arbitrarily_large_small_ratio',
        'jsp_000393', 'complex_original']
}
if len(reports) != len(expected) or {x[0] for x in reports} != expected:
    raise SystemExit('Missing or unexpected general-field axiom reports')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in reports:
    actual = {x.strip() for x in axioms.split(',') if x.strip()}
    if not actual <= allowed:
        raise SystemExit('Unexpected axiom in ' + name + ': ' + str(actual))
print('Passed: 11 general-field axiom-closure audits', flush=True)

for module in ['ErdosProblems.Erdos485', 'JSP000393',
               'JSP000393Complete', 'JSP000393General']:
    run(['lake', 'env', 'leanchecker', '--verbose', module],
        'kernel-' + module + '.log')

negative = EVIDENCE / 'Negative.lean'
negative.write_text('import JSP000393General\nexample : (1 : Nat) = 0 := by decide\n')
result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(negative)],
                        capture_output=True, text=True)
(EVIDENCE / 'negative-control.log').write_text(result.stdout + result.stderr)
if result.returncode == 0 or 'error:' not in result.stdout + result.stderr:
    raise SystemExit('False-arithmetic control was not rejected as expected')
negative.unlink()
print('Passed: false-arithmetic negative control', flush=True)
sources = [ROOT / (x.replace('.', '/') + '.lean')
           for x in original['modules_compiled'] + ['JSP000393General', 'AuditGeneral']]
record = {
    'status': 'passed',
    'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
    'preparation_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'modules_compiled': original['modules_compiled'] + ['JSP000393General', 'AuditGeneral'],
    'original_axiom_reports': original['axiom_reports'],
    'general_axiom_reports': len(reports),
    'allowed_axioms': sorted(allowed),
    'dependency_count': original['dependency_count'],
    'kernel_prefixes': ['ErdosProblems.Erdos485', 'JSP000393',
                        'JSP000393Complete', 'JSP000393General'],
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sources},
    'limits': 'Contributor-run replay with cached pinned Mathlib; no independent human certification.'
}
(EVIDENCE / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
