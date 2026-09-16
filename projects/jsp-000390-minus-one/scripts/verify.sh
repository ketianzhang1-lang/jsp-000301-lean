#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
export LEAN_NUM_THREADS=1
lake build --wfail 2>&1 | tee evidence/build.log
lake env leanchecker JSP000390 2>&1 | tee evidence/leanchecker.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 - <<'PY'
from pathlib import Path
import hashlib, json, re
names = ["three_pow_succ_dvd", "three_pow_is_solution", "minus_one_unbounded",
         "minus_one_infinite", "minus_one_infinite_unrestricted"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
log = Path("evidence/axioms.log").read_text()
reports = {}
for name in names:
    full = "JSP000390." + name
    match = re.search(r"'" + re.escape(full) + r"' depends on axioms: \[([^\]]*)\]", log)
    if not match:
        raise SystemExit("Missing actual axiom report for " + full)
    axioms = {s.strip() for s in match.group(1).split(",") if s.strip()}
    if not axioms <= allowed:
        raise SystemExit("Unexpected axioms for " + full + ": " + repr(axioms))
    reports[full] = sorted(axioms)
source = Path("JSP000390.lean").read_text()
if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source):
    raise SystemExit("Prohibited proof construct found in JSP000390.lean")
manifest = json.loads(Path("lake-manifest.json").read_text())
assert manifest["name"] == "JSP000390"
for package in manifest["packages"]:
    import subprocess
    actual = subprocess.check_output(["git", "-C", ".lake/packages/" + package["name"],
                                      "rev-parse", "HEAD"], text=True).strip()
    if actual != package["rev"]:
        raise SystemExit("Dependency pin mismatch: " + package["name"])
Path("evidence/axiom-audit.json").write_text(json.dumps(reports, indent=2) + "\n")
paths = ["JSP000390.lean", "Audit.lean", "lakefile.lean", "lean-toolchain",
         "lake-manifest.json", "scripts/verify.sh", "scripts/verify_nanoda.sh"]
Path("evidence/SOURCE_SHA256SUMS").write_text("".join(
    hashlib.sha256(Path(p).read_bytes()).hexdigest() + "  " + p + "\n" for p in paths))
print("All five target-axiom audits and all dependency pin checks passed.")
PY
# Confirm a false proposition is rejected by the same Lean invocation.
printf 'import JSP000390\nexample : (1 : Nat) = 0 := by decide\n' > NegativeControl.lean
if lake env lean NegativeControl.lean > evidence/negative-control.log 2>&1; then
  rm -f NegativeControl.lean
  echo 'ERROR: false arithmetic was accepted' >&2
  exit 1
fi
rm -f NegativeControl.lean
printf 'False arithmetic rejected as expected.\n' >> evidence/negative-control.log
