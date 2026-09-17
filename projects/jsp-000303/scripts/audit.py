"""Validate actual Lean axiom reports against an explicit target list."""
import re, sys
from pathlib import Path
expected = {'JSP000303.alpha_congruence', 'JSP000303.not_quadratic_bound', 'JSP000303.erdos_367_k_three_lower', 'JSP000303.log_witness_le', 'Erdos367.erdos_367.variants.k_ge_three_lower', 'JSP000303.logarithmic_lower_all_k', 'Erdos367.erdos_367.parts.ii', 'JSP000303.ratio_unbounded', 'JSP000303.quantitative_nat', 'JSP000303.logarithmic_bound', 'JSP000303.prime_power_divides'}
text = Path(sys.argv[1]).read_text()
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
assert {name for name, _ in found} == expected, 'Missing or unexpected audit target'
assert len(found) == len(expected), 'Duplicate audit target'
for name, axioms in found:
    actual = {a.strip() for a in axioms.split(',') if a.strip()}
    assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
print('PASS: all 11 declarations use only standard foundational axioms')
