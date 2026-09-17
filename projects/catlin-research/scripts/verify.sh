#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
for module in Certificate GraphCore Profile Subdivision Colouring Catlin Sharp; do
  lake env leanchecker "$module"
done 2>&1 | tee evidence/leanchecker.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
import re,json,subprocess
from pathlib import Path
names=re.findall(r'^#print axioms (\S+)',Path('Audit.lean').read_text(),re.M)
assert len(names)==12
log=Path('evidence/axioms.log').read_text()
for name in names:
    if "'"+name+"' does not depend on any axioms" in log:
        continue
    m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
    assert m is not None,name
    assert {x.strip() for x in m[1].split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},name
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    assert subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()==pkg['rev']
print('All twelve axiom audits and all actual dependency revisions passed.')
PY
printf 'import Sharp\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic was accepted' >&2
  exit 1
fi
echo 'False-arithmetic negative control rejected as expected.'
