#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
python3 - <<'PY2'
import json,subprocess
from pathlib import Path
modules=json.loads(Path('UPSTREAM_MODULES.json').read_text())+['JSP000465']
with Path('evidence/leanchecker.log').open('w') as out:
    for module in modules:
        print('KERNEL REPLAY',module,flush=True)
        out.write('KERNEL REPLAY '+module+'\n');out.flush()
        subprocess.run(['lake','env','leanchecker',module],stdout=out,stderr=subprocess.STDOUT,check=True)
PY2
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
import re,json,subprocess
from pathlib import Path
names=re.findall(r'^#print axioms (\S+)',Path('Audit.lean').read_text(),re.M)
assert len(names)==7
log=Path('evidence/axioms.log').read_text()
for name in names:
    m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
    assert m is not None,name
    assert {x.strip() for x in m[1].split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},name
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    assert subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()==pkg['rev']
print('All seven axiom audits and all actual dependency revisions passed.')
PY
printf 'import JSP000465\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic was accepted' >&2
  exit 1
fi
