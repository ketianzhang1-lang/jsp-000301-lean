#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker JSP000476 2>&1 | tee evidence/kernel.log
lake env lean Examples.lean 2>&1 | tee evidence/examples.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 scripts/audit.py | tee evidence/audit-result.log
python3 scripts/crosscheck.py | tee evidence/crosscheck.json
python3 - <<'PY'
from pathlib import Path
import json, subprocess
for package in json.loads(Path('lake-manifest.json').read_text())['packages']:
    head = subprocess.check_output(['git', '-C', '.lake/packages/' + package['name'],
                                    'rev-parse', 'HEAD'], text=True).strip()
    assert head == package['rev'], (package['name'], head)
print('Every dependency revision matches the committed manifest.')
Path('Negative.lean').write_text('import JSP000476\nexample : (1 : Nat) = 0 := by decide\n')
PY
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: false arithmetic was accepted' >&2
  exit 1
fi
python3 - <<'PY'
from pathlib import Path
text = Path('evidence/negative-control.log').read_text()
assert 'error' in text and 'decide' in text, text
Path('Negative.lean').unlink()
print('Negative control rejected as expected.')
PY
