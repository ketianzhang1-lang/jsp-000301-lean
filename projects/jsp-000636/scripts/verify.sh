#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker JSP000636 2>&1 | tee evidence/leanchecker.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
import json, re, subprocess
from pathlib import Path
source = Path('JSP000636.lean').read_text()
decls = re.findall(r'^theorem (\w+)', source, re.M)
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert names == ['JSP000636.' + x for x in decls]
assert len(names) == 14
log = Path('evidence/axioms.log').read_text()
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if m:
        assert {x.strip() for x in m[1].split(',') if x.strip()} <= {
            'propext', 'Classical.choice', 'Quot.sound'}, name
    else:
        assert "'" + name + "' does not depend on any axioms" in log, name
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    actual = subprocess.check_output(
        ['git', '-C', '.lake/packages/' + pkg['name'], 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == pkg['rev'], (pkg['name'], actual, pkg['rev'])
print('All 14 theorem axiom audits and dependency pins passed.')
PY
printf 'import JSP000636\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: false arithmetic was accepted' >&2
  exit 1
fi
echo 'False arithmetic rejected as required.'
