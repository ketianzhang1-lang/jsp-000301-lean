#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence-selection
export LEAN_NUM_THREADS=1
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
pin() {
  local url=$1 sha=$2 dir=$3
  git init -q "$dir"
  git -C "$dir" remote add origin "$url"
  git -C "$dir" fetch -q --depth 1 origin "$sha"
  git -C "$dir" checkout -q --detach FETCH_HEAD
  test "$(git -C "$dir" rev-parse HEAD)" = "$sha"
  printf '%s %s\n' "$url" "$sha"
}
pin https://github.com/leanprover/lean4export.git 8554815c2dc6b7abe99ec1f08849c9759ba77947 "$work/exporter"
pin https://github.com/ammkrn/nanoda_lib.git 4c544ed4099c8227f07d5de77ad1e69fb0740a27 "$work/checker"
cp lean-toolchain "$work/exporter/lean-toolchain"
(cd "$work/exporter" && lake build)
(cd "$work/checker" && cargo build --release --locked)
mapfile -t targets < <(python3 -c 'import json;print("\n".join(json.load(open("SELECTION_TARGETS.json"))))')
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000506Selection -- "${targets[@]}" > evidence-selection/export.ndjson
python3 - <<'PY'
import json
from pathlib import Path
config={
  'export_file_path':'evidence-selection/export.ndjson','use_stdin':False,
  'permitted_axioms':['propext','Classical.choice','Quot.sound'],
  'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
  'pp_declars':json.loads(Path('SELECTION_TARGETS.json').read_text()),
  'pp_output_path':'evidence-selection/nanoda-statements.txt','pp_to_stdout':False,'print_success_message':True}
Path('evidence-selection/nanoda-config.json').write_text(json.dumps(config,indent=2)+'\n')
Path('evidence-selection/nanoda-statements.txt').write_text('')
PY
"$work/checker/target/release/nanoda_bin" evidence-selection/nanoda-config.json 2>&1 | tee evidence-selection/nanoda.log
python3 - <<'PY'
import re
from pathlib import Path
assert re.search(r'Checked [0-9]+ declarations with no errors', Path('evidence-selection/nanoda.log').read_text())
assert Path('evidence-selection/nanoda-statements.txt').stat().st_size > 0
PY
gzip -n -f evidence-selection/export.ndjson
sha256sum evidence-selection/export.ndjson.gz evidence-selection/nanoda-config.json > evidence-selection/CHECKER_SHA256SUMS

printf "Strict NaNoda verification passed for 60 original and supplementary target closures.\n"
