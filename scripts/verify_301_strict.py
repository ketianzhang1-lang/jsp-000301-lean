"""Strict replay and dependency/axiom audit of the unchanged original proof."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

os.chdir(Path(__file__).resolve().parents[1])
os.environ['LEAN_NUM_THREADS'] = '1'
out = Path('evidence/strict-301')
out.mkdir(parents=True, exist_ok=True)
pin = 'e1a17b0d6728b9d4929d1d4abd3721a27377369a'
bound = ['JSP000301.lean', 'lake-manifest.json', 'lean-toolchain', 'lakefile.lean']
hashes = {}
for name in bound:
    historical = subprocess.check_output(['git', 'show', pin + ':' + name])
    current = Path(name).read_bytes()
    if current != historical:
        raise SystemExit('Original source/configuration binding failed: ' + name)
    hashes[name] = hashlib.sha256(current).hexdigest()

def run(args, name):
    with (out / name).open('w') as log:
        result = subprocess.run(args, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print((out / name).read_text()[-12000:], flush=True)
        raise SystemExit('Failed: ' + ' '.join(args))
    print('Passed: ' + ' '.join(args), flush=True)

run(['lake', 'build', '--wfail'], 'build.log')
manifest = json.loads(Path('lake-manifest.json').read_text())
if len(manifest['packages']) != 9:
    raise SystemExit('Unexpected number of locked dependencies')
for package in manifest['packages']:
    actual = subprocess.check_output(['git', '-C', '.lake/packages/' + package['name'],
                                     'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit('Dependency revision differs: ' + package['name'])
run(['lake', 'env', 'leanchecker', '--verbose', 'JSP000301'], 'kernel.log')
run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Audit301Strict.lean'], 'axioms.log')
targets = re.findall(r'^#print axioms (\S+)', Path('Audit301Strict.lean').read_text(), re.M)
if len(targets) != 8 or len(set(targets)) != 8:
    raise SystemExit('Expected eight distinct public targets')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
log = (out / 'axioms.log').read_text()
for name in targets:
    match = re.search("'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", log)
    if match:
        if not {x.strip() for x in match[1].split(',') if x.strip()} <= allowed:
            raise SystemExit('Unpermitted axiom: ' + name)
    elif "'" + name + "' does not depend on any axioms" not in log:
        raise SystemExit('Missing axiom report: ' + name)
negative = Path('Negative301Strict.lean')
negative.write_text('import JSP000301\nexample : (1 : Nat) = 0 := by decide\n')
try:
    result = subprocess.run(['lake', 'env', 'lean', str(negative)], capture_output=True, text=True)
finally:
    negative.unlink()
negative_log = result.stdout + result.stderr
(out / 'negative-control.log').write_text(negative_log)
if result.returncode == 0 or 'is false' not in negative_log:
    raise SystemExit('Negative control did not fail for the expected false proposition')
for name, digest in hashes.items():
    if hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest:
        raise SystemExit('Source/configuration changed during verification: ' + name)
record = {'status': 'passed', 'source_commit': pin,
          'verification_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
          'toolchain': Path('lean-toolchain').read_text().strip(), 'targets': targets,
          'allowed_axioms': sorted(allowed), 'source_sha256': hashes, 'dependency_count': 9,
          'limits': 'Contributor-run automated verification; no independent human certification.'}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print('Strict build, replay, eight axiom reports, nine dependencies and negative control passed.', flush=True)
