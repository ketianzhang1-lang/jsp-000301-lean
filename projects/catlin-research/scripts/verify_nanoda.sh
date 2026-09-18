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
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000585Complete -- \
  CatlinCertificates.eight_colours CatlinCertificates.proper_eight_colouring CatlinCertificates.no_independent_triple CatlinCertificates.finite_budget_certificate CatlinCertificates.budget_bound CatlinCertificates.no_feasible_resource_tuple CatlinComplete.mem_inside CatlinComplete.card_inside CatlinComplete.length_ge_two CatlinComplete.length_ge_three CatlinComplete.demand_le_inside CatlinComplete.profile_certificate CatlinComplete.separated_endpoints CatlinComplete.common_in_middle CatlinComplete.cluster_size CatlinComplete.count_le_three CatlinComplete.sum_counts CatlinComplete.full_cluster CatlinComplete.weight_le_demand CatlinComplete.regroup CatlinComplete.regroup_twice CatlinComplete.profileCost_le_budget CatlinComplete.budget_ge_eight CatlinComplete.sum_demand_edges CatlinComplete.total_inside_bound CatlinComplete.subdivision_budget_bound CatlinComplete.colour_fiber_card_le_two CatlinComplete.not_seven_colorable CatlinComplete.chromaticNumber_eq_eight CatlinComplete.no_K8_subdivision CatlinComplete.catlin_counterexample CatlinComplete.seven_exceptional CatlinComplete.seven_detour CatlinComplete.contains_K7_subdivision CatlinComplete.containsCliqueSubdivision_antitone CatlinComplete.containsCliqueSubdivision_iff CatlinComplete.sharp_catlin_counterexample JSP000585.edge_left_mem JSP000585.edge_right_mem JSP000585.edge_lt JSP000585.card_branchSet JSP000585.mem_branchSet JSP000585.branch_branchLabel JSP000585.labels_ne JSP000585.indexedEdge_injective JSP000585.convertedPath_isPath JSP000585.inside_convertedPath JSP000585.containsSubdivision_iff_indexed JSP000585.subdivisionModels_iff JSP000585.catlin_subdivision_iff JSP000585.catlin_sigma_eq_seven JSP000585.catlin_chi_eq_eight JSP000585.catlin_ratio_eq JSP000585.catlin_ratio_gt_one JSP000585.exists_universal_ratio_bound JSP000585.ratio_range_bddAbove JSP000585.extremal_upper_bound JSP000585.catlin_extremal_lower_bound JSP000585.catlin_constant_lower_bound JSP000585.jsp_000585 Erdos717.erdos_717 > evidence/export.ndjson
python3 - <<'PY'
import json
from pathlib import Path
config={
  'export_file_path':'evidence/export.ndjson','use_stdin':False,
  'permitted_axioms':['propext','Classical.choice','Quot.sound'],
  'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
  'pp_declars':['CatlinCertificates.eight_colours', 'CatlinCertificates.proper_eight_colouring', 'CatlinCertificates.no_independent_triple', 'CatlinCertificates.finite_budget_certificate', 'CatlinCertificates.budget_bound', 'CatlinCertificates.no_feasible_resource_tuple', 'CatlinComplete.mem_inside', 'CatlinComplete.card_inside', 'CatlinComplete.length_ge_two', 'CatlinComplete.length_ge_three', 'CatlinComplete.demand_le_inside', 'CatlinComplete.profile_certificate', 'CatlinComplete.separated_endpoints', 'CatlinComplete.common_in_middle', 'CatlinComplete.cluster_size', 'CatlinComplete.count_le_three', 'CatlinComplete.sum_counts', 'CatlinComplete.full_cluster', 'CatlinComplete.weight_le_demand', 'CatlinComplete.regroup', 'CatlinComplete.regroup_twice', 'CatlinComplete.profileCost_le_budget', 'CatlinComplete.budget_ge_eight', 'CatlinComplete.sum_demand_edges', 'CatlinComplete.total_inside_bound', 'CatlinComplete.subdivision_budget_bound', 'CatlinComplete.colour_fiber_card_le_two', 'CatlinComplete.not_seven_colorable', 'CatlinComplete.chromaticNumber_eq_eight', 'CatlinComplete.no_K8_subdivision', 'CatlinComplete.catlin_counterexample', 'CatlinComplete.seven_exceptional', 'CatlinComplete.seven_detour', 'CatlinComplete.contains_K7_subdivision', 'CatlinComplete.containsCliqueSubdivision_antitone', 'CatlinComplete.containsCliqueSubdivision_iff', 'CatlinComplete.sharp_catlin_counterexample', 'JSP000585.edge_left_mem', 'JSP000585.edge_right_mem', 'JSP000585.edge_lt', 'JSP000585.card_branchSet', 'JSP000585.mem_branchSet', 'JSP000585.branch_branchLabel', 'JSP000585.labels_ne', 'JSP000585.indexedEdge_injective', 'JSP000585.convertedPath_isPath', 'JSP000585.inside_convertedPath', 'JSP000585.containsSubdivision_iff_indexed', 'JSP000585.subdivisionModels_iff', 'JSP000585.catlin_subdivision_iff', 'JSP000585.catlin_sigma_eq_seven', 'JSP000585.catlin_chi_eq_eight', 'JSP000585.catlin_ratio_eq', 'JSP000585.catlin_ratio_gt_one', 'JSP000585.exists_universal_ratio_bound', 'JSP000585.ratio_range_bddAbove', 'JSP000585.extremal_upper_bound', 'JSP000585.catlin_extremal_lower_bound', 'JSP000585.catlin_constant_lower_bound', 'JSP000585.jsp_000585', 'Erdos717.erdos_717'],
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
