#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker JSP000780 2>&1 | tee evidence/kernel-main.log
lake env leanchecker Audit 2>&1 | tee evidence/kernel-audit.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PYCODE'
from pathlib import Path
import json, re, subprocess
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(names) == 6
log = Path('evidence/axioms.log').read_text()
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if m:
        axioms = {s.strip() for s in m[1].split(',') if s.strip()}
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    else:
        assert "'" + name + "' does not depend on any axioms" in log, name
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    head = subprocess.check_output(['git', '-C', '.lake/packages/'+pkg['name'],
                                   'rev-parse', 'HEAD'], text=True).strip()
    assert head == pkg['rev'], (pkg['name'], head)
print('Six target axiom audits and nine dependency revision checks passed.')
PYCODE
printf 'import JSP000780\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic was accepted' >&2
  exit 1
fi
sha256sum JSP000780.lean Audit.lean lakefile.lean lean-toolchain lake-manifest.json > evidence/SOURCE_SHA256SUMS
