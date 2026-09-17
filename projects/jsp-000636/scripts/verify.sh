#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
for module in JSP000636 Lower Upper Construction Threshold Thinning; do
  lake env leanchecker "$module" 2>&1 | tee "evidence/leanchecker-$module.log"
done
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
import json, re, subprocess
from pathlib import Path
source = '\n'.join(Path(f).read_text() for f in ['JSP000636.lean', 'Lower.lean', 'Upper.lean', 'Construction.lean', 'Threshold.lean', 'Thinning.lean'])
decls = re.findall(r'^theorem (\w+)', source, re.M)
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert [x.rsplit('.', 1)[-1] for x in names] == decls
assert len(names) == 61
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
print('All 61 theorem axiom audits and dependency pins passed.')
PY
printf 'import Thinning\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: false arithmetic was accepted' >&2
  exit 1
fi
echo 'False arithmetic rejected as required.'
