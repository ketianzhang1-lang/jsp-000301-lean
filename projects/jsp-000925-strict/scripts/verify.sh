#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
mkdir -p evidence
python3 scripts/bootstrap.py | tee evidence/bootstrap.log
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker Erdos1114 2>&1 | tee evidence/upstream-kernel.log
lake env leanchecker JSP000925Strict 2>&1 | tee evidence/supplement-kernel.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
import re, json, subprocess, hashlib
from pathlib import Path
names=re.findall(r'^#print axioms (\S+)',Path('Audit.lean').read_text(),re.M)
assert len(names)==8
log=Path('evidence/axioms.log').read_text()
for name in names:
    m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
    assert m is not None, name
    assert {x.strip() for x in m[1].split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, name
for p in json.loads(Path('lake-manifest.json').read_text())['packages']:
    assert subprocess.check_output(['git','-C','.lake/packages/'+p['name'],'rev-parse','HEAD'],text=True).strip()==p['rev']
print('Eight axiom audits and all dependency pins passed.')
print('Supplement SHA256:',hashlib.sha256(Path('JSP000925Strict.lean').read_bytes()).hexdigest())
PY
printf 'import JSP000925Strict\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative.log 2>&1; then
  echo 'Invalid arithmetic unexpectedly accepted'; exit 1
fi
