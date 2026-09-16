#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
export LEAN_NUM_THREADS=1
lake build --wfail 2>&1 | tee evidence/build.log
for module in JSP000617 JSP000617Cover JSP000617Sparse; do
  lake env leanchecker "$module" 2>&1 | tee "evidence/leanchecker-$module.log"
done
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
import re,json,subprocess,hashlib
from pathlib import Path
names=['sum_sq_collision','pairSumFiber_card_le_two','parabolaSumset_large',
       'translated_representations_le_two','curveUnion_representations_le',
       'sum_misses','exists_halving_translate','exists_small_uncovered','finite_plane_construction',
       'squareFiber_card_le_two','translated_row_card_le_two','curveUnion_row_card_le',
       'finite_plane_construction_sparse']
log=Path('evidence/axioms.log').read_text()
allowed={'propext','Classical.choice','Quot.sound'}
reports={}
for name in names:
    full='JSP000617.'+name
    m=re.search("'"+re.escape(full)+r"' depends on axioms: \[([^\]]*)\]",log)
    assert m, full
    ax={a.strip() for a in m[1].split(',') if a.strip()}
    assert ax<=allowed,(full,ax)
    reports[full]=sorted(ax)
for f in ['JSP000617.lean','JSP000617Cover.lean','JSP000617Sparse.lean']:
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b',Path(f).read_text()),f
for pkg in json.loads(Path('lake-manifest.json').read_text())['packages']:
    actual=subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()
    assert actual==pkg['rev'],pkg['name']
Path('evidence/axiom-audit.json').write_text(json.dumps(reports,indent=2)+'\n')
print('All thirteen actual target-axiom reports and nine dependency pins checked.')
PY
printf 'import JSP000617Sparse\nexample : (1 : Nat) = 0 := by decide\n' > NegativeControl.lean
if lake env lean NegativeControl.lean > evidence/negative-control.log 2>&1; then
  rm NegativeControl.lean
  echo 'ERROR: false arithmetic accepted' >&2
  exit 1
fi
rm NegativeControl.lean
printf '\nFalse arithmetic rejected as expected.\n' >> evidence/negative-control.log
