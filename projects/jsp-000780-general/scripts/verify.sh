#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker Adapter 2>&1 | tee evidence/kernel-adapter.log
lake env leanchecker Audit 2>&1 | tee evidence/kernel-audit.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 scripts/audit.py
sha256sum Core.lean Coefficients.lean Separation.lean Construction.lean Main.lean Adapter.lean Audit.lean lakefile.lean lean-toolchain lake-manifest.json > evidence/SOURCE_SHA256SUMS
