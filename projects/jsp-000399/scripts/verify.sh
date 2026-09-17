#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
lake build --wfail 2>&1 | tee evidence/build.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
lake env leanchecker JSP000399 2>&1 | tee evidence/leanchecker.log
