from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
targets = re.findall(r'^#print axioms (\S+)', (root / 'Audit.lean').read_text(), re.M)
source_names = re.findall(r'^(?:@\[simp\] )?(?:theorem|def) (\w+)',
                          (root / 'JSP000476.lean').read_text(), re.M)
assert set(targets) == {'JSP000476.' + n for n in source_names}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
log = (root / 'evidence/axioms.log').read_text()
for target in targets:
    match = re.search("'" + re.escape(target) + r"' depends on axioms: \[([^\]]*)\]", log)
    if match:
        axioms = {x.strip() for x in match[1].split(',') if x.strip()}
        assert axioms <= allowed, (target, axioms)
    else:
        assert "'" + target + "' does not depend on any axioms" in log, target
print(f'All {len(targets)} project declarations passed the transitive axiom allowlist.')
