#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence/ci
sha256sum -c SOURCE_SHA256SUMS
lake build --wfail 2>&1 | tee evidence/ci/build.log
for module in JSP000749.Counting JSP000749.Estimates JSP000749.Construction JSP000749.Main JSP000749 StatementCheck; do
  lake env leanchecker "$module" 2>&1 | tee "evidence/ci/leanchecker-${module}.log"
done
lake env lean -E warning Audit.lean 2>&1 | tee evidence/ci/axioms.log
lake env lean -E warning StatementCheck.lean 2>&1 | tee evidence/ci/statement-check.log
python3 - <<'PY'
from pathlib import Path
import json, re, subprocess
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(names) == 11, names
names.append('JSP000749StatementCheck.plain_upper_bound')
log = Path('evidence/ci/axioms.log').read_text() + Path('evidence/ci/statement-check.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    assert m, 'Missing target axiom report: ' + name
    actual = {x.strip() for x in m[1].split(',') if x.strip()}
    assert actual <= allowed, (name, actual)
packages = json.loads(Path('lake-manifest.json').read_text())['packages']
for pkg in packages:
    head = subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()
    assert head == pkg['rev'], (pkg['name'], head)
print(f'PASS: {len(names)} target axiom closures and {len(packages)} actual dependency pins.')
PY
printf 'import JSP000749\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/ci/negative-control.log 2>&1; then
  echo 'ERROR: false arithmetic was accepted' >&2
  exit 1
fi
python3 scripts/crosscheck.py | tee evidence/ci/diagnostics.log
