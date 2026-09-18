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
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000140Complete -- \
  JSP000140.card_le_four JSP000140.bad_quad JSP000140.triangle_not_mono JSP000140.fork_center_unique JSP000140.fork_swap JSP000140.fork_centers_not_adjacent JSP000140.fork_closing_isolated JSP000140.fork_closing_unique JSP000140.edgeImage_injective JSP000140.edgeImage_mem JSP000140.fork_packing JSP000140.fork_card_eq JSP000140.sum_degree JSP000140.quadratic_degree_bound JSP000140.incidence_bound JSP000140.lower_bound JSP000140.fork_absent_color JSP000140.strict_incidence_bound JSP000140.strict_lower_bound JSP000140.integer_lower_bound JSP000140.edgeColors_four JSP000140.lower_bound_from_vertex_sets JSP000140.four_edges JSP000140.pullback_topEdge JSP000140.six_image JSP000140.toEdges_apply JSP000140.toEdges_admissible JSP000140.fromEdges_apply JSP000140.fromEdges_symm JSP000140.fromEdges_admissible JSP000140.edge_palette_pos JSP000140.pairColorable_iff JSP000140.pairColorable_nonempty JSP000140.minPalette_spec JSP000140.minPalette_le JSP000140.minPalette_eq JSP000140.minPalette_strict_lower JSP000140.minPalette_integer_lower JSP000140.minPalette_tendsto JSP000140.minPalette_asymptotic JSP000140.eventually_near_optimal JSP000140.upstream_strict_lower JSP000140.upstream_integer_lower JSP000140.jsp_000140 Erdos136.erdos_136 Erdos136.erdos136_asymptotic > evidence/export.ndjson
python3 - <<'PY'
import json
from pathlib import Path
config={
  'export_file_path':'evidence/export.ndjson','use_stdin':False,
  'permitted_axioms':['propext','Classical.choice','Quot.sound'],
  'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
  'pp_declars':['JSP000140.card_le_four', 'JSP000140.bad_quad', 'JSP000140.triangle_not_mono', 'JSP000140.fork_center_unique', 'JSP000140.fork_swap', 'JSP000140.fork_centers_not_adjacent', 'JSP000140.fork_closing_isolated', 'JSP000140.fork_closing_unique', 'JSP000140.edgeImage_injective', 'JSP000140.edgeImage_mem', 'JSP000140.fork_packing', 'JSP000140.fork_card_eq', 'JSP000140.sum_degree', 'JSP000140.quadratic_degree_bound', 'JSP000140.incidence_bound', 'JSP000140.lower_bound', 'JSP000140.fork_absent_color', 'JSP000140.strict_incidence_bound', 'JSP000140.strict_lower_bound', 'JSP000140.integer_lower_bound', 'JSP000140.edgeColors_four', 'JSP000140.lower_bound_from_vertex_sets', 'JSP000140.four_edges', 'JSP000140.pullback_topEdge', 'JSP000140.six_image', 'JSP000140.toEdges_apply', 'JSP000140.toEdges_admissible', 'JSP000140.fromEdges_apply', 'JSP000140.fromEdges_symm', 'JSP000140.fromEdges_admissible', 'JSP000140.edge_palette_pos', 'JSP000140.pairColorable_iff', 'JSP000140.pairColorable_nonempty', 'JSP000140.minPalette_spec', 'JSP000140.minPalette_le', 'JSP000140.minPalette_eq', 'JSP000140.minPalette_strict_lower', 'JSP000140.minPalette_integer_lower', 'JSP000140.minPalette_tendsto', 'JSP000140.minPalette_asymptotic', 'JSP000140.eventually_near_optimal', 'JSP000140.upstream_strict_lower', 'JSP000140.upstream_integer_lower', 'JSP000140.jsp_000140', 'Erdos136.erdos_136', 'Erdos136.erdos136_asymptotic'],
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
