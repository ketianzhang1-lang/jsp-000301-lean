from pathlib import Path
import json, re, subprocess, sys
names = re.findall(r"^#print axioms (\S+)", Path("Audit.lean").read_text(), re.M)
log = Path("evidence/axioms.log").read_text()
assert len(names) == 5
for name in names:
    m = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    assert m, name
    axioms = {s.strip() for s in m[1].split(",") if s.strip()}
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, (name, axioms)
root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".lake/packages")
for pkg in json.loads(Path("lake-manifest.json").read_text())["packages"]:
    head = subprocess.check_output(["git", "-C", str(root / pkg["name"]), "rev-parse", "HEAD"], text=True).strip()
    assert head == pkg["rev"], (pkg["name"], head)
print("PASS: five target axiom audits and nine dependency revision checks.")
