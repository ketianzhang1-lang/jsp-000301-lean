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
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000725Complete -- \
  JSP000725.sum_lower JSP000725.sum_upper JSP000725.interval_ordered_sums JSP000725.interval_admissible JSP000725.interval_card JSP000725.length_le_endpoint JSP000725.construction_for_every_N JSP000725.even_length_family JSP000725.sum_block JSP000725.boundary_obstruction JSP000725.card_toInt JSP000725.sum_toInt JSP000725.admissible_iff_cardinality_determined JSP000725.admissible_iff_upstream JSP000725.bounded_iff JSP000725.boundedAdmissible_iff JSP000725.exists_nat_preimage JSP000725.mem_admissibleFamily JSP000725.maxCard_eq_upstream JSP000725.strausLength_feasible JSP000725.terminalInterval_spec JSP000725.card_le_maxCard JSP000725.eventual_maxCard_exact JSP000725.eventual_terminalInterval_optimal JSP000725.maxCard_asymptotic JSP000725.jsp_000725 Erdos874.erdos_874_eventual_exact Erdos874.erdos_874 > evidence/export.ndjson
python3 - <<'PY'
import json
from pathlib import Path
config={
  'export_file_path':'evidence/export.ndjson','use_stdin':False,
  'permitted_axioms':['propext','Classical.choice','Quot.sound'],
  'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
  'pp_declars':['JSP000725.sum_lower', 'JSP000725.sum_upper', 'JSP000725.interval_ordered_sums', 'JSP000725.interval_admissible', 'JSP000725.interval_card', 'JSP000725.length_le_endpoint', 'JSP000725.construction_for_every_N', 'JSP000725.even_length_family', 'JSP000725.sum_block', 'JSP000725.boundary_obstruction', 'JSP000725.card_toInt', 'JSP000725.sum_toInt', 'JSP000725.admissible_iff_cardinality_determined', 'JSP000725.admissible_iff_upstream', 'JSP000725.bounded_iff', 'JSP000725.boundedAdmissible_iff', 'JSP000725.exists_nat_preimage', 'JSP000725.mem_admissibleFamily', 'JSP000725.maxCard_eq_upstream', 'JSP000725.strausLength_feasible', 'JSP000725.terminalInterval_spec', 'JSP000725.card_le_maxCard', 'JSP000725.eventual_maxCard_exact', 'JSP000725.eventual_terminalInterval_optimal', 'JSP000725.maxCard_asymptotic', 'JSP000725.jsp_000725', 'Erdos874.erdos_874_eventual_exact', 'Erdos874.erdos_874'],
  'pp_output_path':'evidence/nanoda-statements.txt','pp_to_stdout':False,'print_success_message':True}
Path('evidence/nanoda-config.json').write_text(json.dumps(config,indent=2)+'\n')
Path('evidence/nanoda-statements.txt').write_text('')
PY
"$work/checker/target/release/nanoda_bin" evidence/nanoda-config.json 2>&1 | tee evidence/nanoda.log
python3 - <<'PY'
import re
from pathlib import Path
assert re.search(r'Checked [0-9]+ declarations with no errors', Path('evidence/nanoda.log').read_text())
assert Path('evidence/nanoda-statements.txt').stat().st_size > 0
PY
gzip -n -f evidence/export.ndjson
sha256sum evidence/export.ndjson.gz evidence/nanoda-config.json > evidence/CHECKER_SHA256SUMS
