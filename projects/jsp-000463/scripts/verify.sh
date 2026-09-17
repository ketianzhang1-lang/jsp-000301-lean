#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker AllOrders 2>&1 | tee evidence/kernel.log
lake env lean -DwarningAsError=true Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
from pathlib import Path
import re, json, subprocess
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(names) == 18
log = Path('evidence/axioms.log').read_text()
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if m:
        axioms = {s.strip() for s in m[1].split(',') if s.strip()}
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    else:
        assert "'" + name + "' does not depend on any axioms" in log, name
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    head = subprocess.check_output(['git', '-C', '.lake/packages/' + pkg['name'],
                                    'rev-parse', 'HEAD'], text=True).strip()
    assert head == pkg['rev'], (pkg['name'], head)
print('All 18 target axiom audits and nine dependency revision checks passed.')
PY
printf 'import AllOrders\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic accepted' >&2
  exit 1
fi
python3 scripts/crosscheck.py | tee evidence/crosscheck.json
sha256sum JSP000463.lean AllOrders.lean Audit.lean lakefile.lean lake-manifest.json lean-toolchain \
  scripts/verify.sh scripts/verify_nanoda.sh scripts/crosscheck.py > evidence/SHA256SUMS
