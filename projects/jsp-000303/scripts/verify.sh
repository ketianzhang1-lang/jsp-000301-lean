#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker --verbose JSP000303 2>&1 | tee evidence/kernel-proof.log
lake env leanchecker --verbose Statement 2>&1 | tee evidence/kernel-statement.log
lake env lean -DwarningAsError=true Audit.lean 2>&1 | tee evidence/axioms.log
python3 scripts/audit.py evidence/axioms.log
printf 'import Statement\nexample : (1 : Nat) = 0 := by decide\n' > NegativeControl.lean
if lake env lean NegativeControl.lean > evidence/negative-control.log 2>&1; then
  echo 'False statement unexpectedly compiled'; exit 1
fi
grep -q 'error' evidence/negative-control.log
rm NegativeControl.lean
sha256sum JSP000303.lean Statement.lean Audit.lean lake-manifest.json > evidence/SOURCE_SHA256SUMS
