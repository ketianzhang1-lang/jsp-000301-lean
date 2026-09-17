"""Check the actual #print axioms outputs, without changing Lean's environment."""
import re
import sys
from pathlib import Path

expected = {
    'sum_lower', 'sum_upper', 'interval_ordered_sums', 'interval_admissible',
    'interval_card', 'length_le_endpoint', 'construction_for_every_N',
    'even_length_family', 'sum_block', 'boundary_obstruction',
}
text = Path(sys.argv[1]).read_text()
found = re.findall(r"'JSP000725\.([^']+)' depends on axioms: \[([^\]]*)\]", text)
assert {name for name, _ in found} == expected, 'Missing or unexpected audit target'
assert len(found) == len(expected), 'Duplicate audit target'
for name, axioms in found:
    actual = {a.strip() for a in axioms.split(',') if a.strip()}
    assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
print('PASS: all 10 declarations use only standard foundational axioms')
