#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
for module in BoseChowla Audit; do
  lake env leanchecker "$module" 2>&1 | tee "evidence/kernel-$module.log"
done
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
from pathlib import Path
import re, json, subprocess
names = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
if len(names) != 5:
    raise SystemExit('Expected exactly five audited targets')
log = Path('evidence/axioms.log').read_text()
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if not m:
        raise SystemExit('Missing axiom audit: ' + name)
    axioms = {s.strip() for s in m[1].split(',') if s.strip()}
    if not axioms <= {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit(f'Unpermitted axioms for {name}: {axioms}')
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    head = subprocess.check_output(['git', '-C', '.lake/packages/' + pkg['name'],
                                   'rev-parse', 'HEAD'], text=True).strip()
    if head != pkg['rev']:
        raise SystemExit('Dependency revision mismatch: ' + pkg['name'])
print('Five target axiom audits and all locked dependency revisions passed.')
PY
printf 'import BoseChowla\nexample : (1 : Nat) = 0 := by decide\n' > Negative.lean
trap 'rm -f Negative.lean' EXIT
if lake env lean Negative.lean > evidence/negative-control.log 2>&1; then
  echo 'ERROR: invalid arithmetic was accepted' >&2
  exit 1
fi
echo 'False-arithmetic negative control rejected as expected.'
