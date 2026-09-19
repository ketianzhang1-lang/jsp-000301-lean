#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence-complete
mapfile -t targets < <(python3 -c 'import json;print("\n".join(json.load(open("AUDIT_TARGETS.json"))))')
lake env lean --run scripts/replay_targets.lean JSP000476Complete "${targets[@]}" 2>&1 | tee evidence-complete/kernel-targets.log
