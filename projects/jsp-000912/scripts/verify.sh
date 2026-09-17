#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence/current
python3 scripts/check_source_sync.py
sha256sum -c SOURCE_SHA256SUMS
lake build --wfail 2>&1 | tee evidence/current/build.log
for module in FullProof JSP912.Grid JSP912.Construction JSP912.Decay JSP912.Potential JSP912.Main; do
  lake env leanchecker "$module" 2>&1 | tee "evidence/current/leanchecker-$module.log"
done
lake env lean -DwarningAsError=true Audit.lean 2>&1 | tee evidence/current/axioms.log
sed 's/^import FullProof$/import JSP912.Main/' Audit.lean > .lake/AuditModular.lean
lake env lean -DwarningAsError=true .lake/AuditModular.lean 2>&1 | tee evidence/current/axioms-modular.log
python3 - <<'PY'
import json, re, subprocess
from pathlib import Path
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(names) == 7
for filename in ['axioms.log', 'axioms-modular.log']:
    log = Path('evidence/current', filename).read_text()
    for name in names:
        match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
        assert match is not None, (filename, name)
        assert {x.strip() for x in match[1].split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, (filename, name)
for package in json.loads(Path('lake-manifest.json').read_text())['packages']:
    actual = subprocess.check_output(['git', '-C', '.lake/packages/' + package['name'], 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == package['rev'], package['name']
print('PASS: seven axiom closures in both proof layouts and all dependency revisions.')
PY
printf 'import FullProof\nexample : (1 : Nat) = 0 := by decide\n' > .lake/Negative.lean
if lake env lean .lake/Negative.lean > evidence/current/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic was accepted' >&2
  exit 1
fi
echo 'PASS: invalid arithmetic negative control was rejected.'
