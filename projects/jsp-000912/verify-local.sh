#!/usr/bin/env bash
# Rebuilds the standalone proof in a clean temporary directory.
# Usage: bash verify-local.sh /absolute/path/to/lean /absolute/path/to/mathlib4
set -euo pipefail
if [[ $# -ne 2 ]]; then
  echo "Usage: $0 /absolute/path/to/lean /absolute/path/to/mathlib4" >&2
  exit 2
fi
LEAN=$(realpath "$1")
MATHLIB=$(realpath "$2")
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
[[ -x "$LEAN" ]] || { echo 'Lean executable is missing.' >&2; exit 2; }
[[ -d "$MATHLIB/.lake/build/lib/lean" ]] || { echo 'Compiled Mathlib is missing.' >&2; exit 2; }
TMP=$(mktemp -d)
trap 'rm -rf -- "$TMP"' EXIT
cp "$HERE/FullProof.lean" "$HERE/Audit.lean" "$TMP/"
export LEAN_PATH="$TMP:$MATHLIB/.lake/build/lib/lean"
for path in "$MATHLIB"/.lake/packages/*/.lake/build/lib/lean; do
  [[ ! -d "$path" ]] || export LEAN_PATH="$LEAN_PATH:$path"
done
cd "$TMP"
"$LEAN" --version
"$LEAN" -DwarningAsError=true -o FullProof.olean FullProof.lean
"$LEAN" -DwarningAsError=true Audit.lean | tee audit.log
python3 - <<'PY'
from pathlib import Path
import re
text=Path('audit.log').read_text()
rows=[line for line in text.splitlines() if 'depends on axioms:' in line]
assert len(rows)==7, f'Expected seven audited results, found {len(rows)}'
expected={'propext','Classical.choice','Quot.sound'}
for row in rows:
    axioms=set(re.search(r'depends on axioms: \[([^\]]*)\]',row).group(1).split(', '))
    assert axioms==expected, f'Unexpected axiom set: {row}'
print('PASS: standalone build, exact-type checks, and all seven axiom audits.')
PY
