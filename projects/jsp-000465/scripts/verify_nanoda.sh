#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
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
pin https://github.com/leanprover/lean4export.git 6cea97789dc088ea47fcea15692db85685aedac5 "$work/exporter"
pin https://github.com/ammkrn/nanoda_lib.git 4c544ed4099c8227f07d5de77ad1e69fb0740a27 "$work/checker"
cp lean-toolchain "$work/exporter/lean-toolchain"
(cd "$work/exporter" && lake build)
(cd "$work/checker" && cargo build --release --locked)
mapfile -t targets < <(python3 -c 'import json; print("\n".join(json.load(open("TARGETS.json"))))')
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000465 -- "${targets[@]}" > evidence/export.ndjson
python3 - <<'PY'
import json
from pathlib import Path
config={
  'export_file_path':'evidence/export.ndjson','use_stdin':False,
  'permitted_axioms':['propext','Classical.choice','Quot.sound'],
  'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
  'pp_declars':json.loads(Path('TARGETS.json').read_text()),
  'pp_output_path':'evidence/nanoda-statements.txt','pp_to_stdout':False,'print_success_message':True}
Path('evidence/nanoda-config.json').write_text(json.dumps(config,indent=2)+'\n')
Path('evidence/nanoda-statements.txt').write_text('')
PY
"$work/checker/target/release/nanoda_bin" evidence/nanoda-config.json 2>&1 | tee evidence/nanoda.log
gzip -n -f evidence/export.ndjson
sha256sum evidence/export.ndjson.gz evidence/nanoda-config.json > evidence/CHECKER_SHA256SUMS
