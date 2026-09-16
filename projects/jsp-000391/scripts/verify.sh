#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker JSP000391 2>&1 | tee evidence/leanchecker-core.log
lake env leanchecker JSP000391Main 2>&1 | tee evidence/leanchecker-main.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'AUDIT'
from pathlib import Path
import re, json, subprocess
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(names) == 8, names
log = Path('evidence/axioms.log').read_text()
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    assert m is not None, 'Missing target audit: ' + name
    axioms = {x.strip() for x in m[1].split(',') if x.strip()}
    assert axioms <= {'propext','Classical.choice','Quot.sound'}, (name, axioms)
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    head = subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()
    assert head == pkg['rev'], (pkg['name'], head)
print('All 8 target axiom audits and all 9 actual dependency pins passed.')
AUDIT
printf 'import JSP000391Main\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic was accepted' >&2
  exit 1
fi
python3 scripts/crosscheck.py | tee evidence/rational-crosscheck.log
