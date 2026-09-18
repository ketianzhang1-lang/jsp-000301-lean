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
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000554Complete -- \
  JSP000554.primorial_pos JSP000554.coprime_primorial_iff JSP000554.minFac_lt_iff_not_coprime JSP000554.prime_coprime_primorial JSP000554.coprime_mod_add JSP000554.badGap_iff_residue JSP000554.badGap_start_ge_length JSP000554.badGap_iff_residue_all JSP000554.count_badGaps JSP000554.count_badGaps_all JSP000554.primorial_values JSP000554.omega_two JSP000554.omega_four JSP000554.omega_six JSP000554.omega_eight JSP000554.omega_ten JSP000554.omega_twelve JSP000554.no_bad_twin_gap JSP000554.gap_four_classification JSP000554.gap_six_classification JSP000554.gap_eight_classification JSP000554.gap_ten_classification JSP000554.gap_twelve_classification JSP000554.lower_add_gap JSP000554.badGap_iff_exceptional JSP000554.badGapIndices_eq JSP000554.mem_goodGapIndices_iff JSP000554.goodGapIndices_eq JSP000554.badGapIndices_density_zero JSP000554.goodGapIndices_density_one JSP000554.badGap_count_ratio_tendsto JSP000554.goodGap_count_ratio_tendsto JSP000554.exceptional_iff_residue JSP000554.mem_residueExceptionIndices_iff JSP000554.jsp_000554 Erdos682.erdos_682 Erdos682.exceptionalGapIndices_density_zero > evidence/export.ndjson
python3 - <<'PY'
import json
from pathlib import Path
config={
  'export_file_path':'evidence/export.ndjson','use_stdin':False,
  'permitted_axioms':['propext','Classical.choice','Quot.sound'],
  'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
  'pp_declars':['JSP000554.primorial_pos', 'JSP000554.coprime_primorial_iff', 'JSP000554.minFac_lt_iff_not_coprime', 'JSP000554.prime_coprime_primorial', 'JSP000554.coprime_mod_add', 'JSP000554.badGap_iff_residue', 'JSP000554.badGap_start_ge_length', 'JSP000554.badGap_iff_residue_all', 'JSP000554.count_badGaps', 'JSP000554.count_badGaps_all', 'JSP000554.primorial_values', 'JSP000554.omega_two', 'JSP000554.omega_four', 'JSP000554.omega_six', 'JSP000554.omega_eight', 'JSP000554.omega_ten', 'JSP000554.omega_twelve', 'JSP000554.no_bad_twin_gap', 'JSP000554.gap_four_classification', 'JSP000554.gap_six_classification', 'JSP000554.gap_eight_classification', 'JSP000554.gap_ten_classification', 'JSP000554.gap_twelve_classification', 'JSP000554.lower_add_gap', 'JSP000554.badGap_iff_exceptional', 'JSP000554.badGapIndices_eq', 'JSP000554.mem_goodGapIndices_iff', 'JSP000554.goodGapIndices_eq', 'JSP000554.badGapIndices_density_zero', 'JSP000554.goodGapIndices_density_one', 'JSP000554.badGap_count_ratio_tendsto', 'JSP000554.goodGap_count_ratio_tendsto', 'JSP000554.exceptional_iff_residue', 'JSP000554.mem_residueExceptionIndices_iff', 'JSP000554.jsp_000554', 'Erdos682.erdos_682', 'Erdos682.exceptionalGapIndices_density_zero'],
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

