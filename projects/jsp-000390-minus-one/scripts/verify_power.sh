#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Retain the complete original k=-1 build/audit and its negative control.
bash scripts/verify.sh
lake env leanchecker JSP000390Power 2>&1 | tee evidence/power-leanchecker.log
lake env lean PowerAudit.lean 2>&1 | tee evidence/power-axioms.log
python3 - <<'PY'
from pathlib import Path
import hashlib, json, re
names = ['power_tail_periodic','exists_zmod_power_period','power_residue_unbounded',
         'power_residue_infinite','powers_of_two_infinite',
         'powers_of_two_infinite_unrestricted','combined_known_families']
allowed = {'propext','Classical.choice','Quot.sound'}
log = Path('evidence/power-axioms.log').read_text()
reports = {}
for name in names:
    full = 'JSP000390Power.' + name
    m = re.search(r"'" + re.escape(full) + r"' depends on axioms: \[([^\]]*)\]", log)
    if not m: raise SystemExit('Missing actual axiom report: ' + full)
    axioms = {s.strip() for s in m.group(1).split(',') if s.strip()}
    if not axioms <= allowed: raise SystemExit('Unexpected axiom: ' + repr(axioms))
    reports[full] = sorted(axioms)
source = Path('JSP000390Power.lean').read_text()
if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', source):
    raise SystemExit('Prohibited proof construct in new module')
Path('evidence/power-axiom-audit.json').write_text(json.dumps(reports, indent=2)+'\n')
paths = ['JSP000390.lean','JSP000390Power.lean','Audit.lean','PowerAudit.lean',
         'lakefile.lean','lean-toolchain','lake-manifest.json','scripts/verify_power.sh',
         'scripts/verify_power_nanoda.sh']
Path('evidence/POWER_SOURCE_SHA256SUMS').write_text(''.join(
    hashlib.sha256(Path(p).read_bytes()).hexdigest()+'  '+p+'\n' for p in paths))
print('All seven supplementary target audits passed.')
PY
