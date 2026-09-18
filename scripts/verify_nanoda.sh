#!/usr/bin/env bash
# Run after the full source compilation and axiom audit.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
evidence=evidence-complete/nanoda
mkdir -p "$evidence"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
pin() {
  local url=$1 sha=$2 dir=$3
  git init -q "$dir"
  git -C "$dir" remote add origin "$url"
  git -C "$dir" fetch -q --depth 1 origin "$sha"
  git -C "$dir" checkout -q --detach FETCH_HEAD
  test "$(git -C "$dir" rev-parse HEAD)" = "$sha"
}
pin https://github.com/leanprover/lean4export.git 6cea97789dc088ea47fcea15692db85685aedac5 "$work/exporter"
pin https://github.com/ammkrn/nanoda_lib.git 4c544ed4099c8227f07d5de77ad1e69fb0740a27 "$work/checker"
cp lean-toolchain "$work/exporter/lean-toolchain"
(cd "$work/exporter" && lake build)
(cd "$work/checker" && cargo build --release --locked)
python3 - "$evidence" <<'PY'
import json, re, sys
from pathlib import Path
out = Path(sys.argv[1])
targets = re.findall(r'^#print axioms (\S+)', Path('AuditComplete.lean').read_text(), re.M)
if len(targets) != 13 or len(set(targets)) != 13:
    raise SystemExit('Unexpected or duplicate audit targets')
(out / 'targets.txt').write_text('\n'.join(targets) + '\n')
config = {
    'export_file_path': str(out / 'export.ndjson'), 'use_stdin': False,
    'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'unpermitted_axiom_hard_error': True,
    'nat_extension': True, 'string_extension': True,
    'pp_declars': targets, 'pp_output_path': str(out / 'statements.txt'),
    'pp_to_stdout': False, 'print_success_message': True,
}
(out / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
(out / 'statements.txt').write_text('')
PY
mapfile -t targets < "$evidence/targets.txt"
lake env "$work/exporter/.lake/build/bin/lean4export" JSP000393Complete -- "${targets[@]}" > "$evidence/export.ndjson"
"$work/checker/target/release/nanoda_bin" "$evidence/config.json" 2>&1 | tee "$evidence/nanoda.log"
python3 - "$evidence" <<'PY'
import datetime, hashlib, json, re, subprocess, sys
from pathlib import Path
out = Path(sys.argv[1])
log = (out / 'nanoda.log').read_text()
match = re.search(r'^Checked (\d+) declarations with no errors\s*$', log, re.M)
if not match or not (out / 'statements.txt').read_text().strip():
    raise SystemExit('NaNoda did not report error-free checking and statement printing')
report = {
    'status': 'passed',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'toolchain': Path('lean-toolchain').read_text().strip(),
    'exporter_commit': '6cea97789dc088ea47fcea15692db85685aedac5',
    'checker_commit': '4c544ed4099c8227f07d5de77ad1e69fb0740a27',
    'module': 'JSP000393Complete', 'targets': (out / 'targets.txt').read_text().splitlines(),
    'declarations_checked': int(match[1]),
    'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'unpermitted_axiom_hard_error': True,
    'export_sha256': hashlib.sha256((out / 'export.ndjson').read_bytes()).hexdigest(),
}
(out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print('Strict NaNoda verification passed for', len(report['targets']), 'target closures.')
PY
gzip -n -f "$evidence/export.ndjson"
sha256sum "$evidence/export.ndjson.gz" "$evidence/config.json" "$evidence/statements.txt" > "$evidence/CHECKER_SHA256SUMS"
