#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker JSP000389 2>&1 | tee evidence/kernel.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
from pathlib import Path
import json, re, subprocess
targets = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(targets) == 8
log = Path('evidence/axioms.log').read_text()
for name in targets:
    match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if match:
        axioms = {a.strip() for a in match[1].split(',') if a.strip()}
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    else:
        assert "'" + name + "' does not depend on any axioms" in log, name
for package in json.loads(Path('lake-manifest.json').read_text())['packages']:
    head = subprocess.check_output(['git', '-C', '.lake/packages/' + package['name'],
                                    'rev-parse', 'HEAD'], text=True).strip()
    assert head == package['rev'], (package['name'], head)
print('All 8 target axiom audits and all dependency revision checks passed.')
PY
printf 'import JSP000389\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: false arithmetic accepted' >&2
  exit 1
fi
python3 -c 'from pathlib import Path; Path("Negative.lean").unlink()'
