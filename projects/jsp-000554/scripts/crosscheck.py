"""Independent finite diagnostic; the quantified statements are proved by Lean."""
from math import gcd, isqrt, prod
import json

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

tables = {
    2: (1, []), 4: (6, [1]), 6: (30, [1, 23]),
    8: (210, [89, 113]), 10: (210, [1, 199]),
    12: (2310, [1, 199, 467, 509, 1789, 1831, 2099, 2297]),
}
report = []
for h, (expected_modulus, expected_residues) in tables.items():
    modulus = prod(q for q in range(h) if prime(q))
    residues = [b for b in range(modulus)
                if gcd(b, modulus) == gcd(b+h, modulus) == 1
                and all(gcd(b+j, modulus) > 1 for j in range(1, h))]
    assert (modulus, residues) == (expected_modulus, expected_residues)
    report.append(dict(gap=h, modulus=modulus, residues=residues))
print(json.dumps({'status': 'PASS', 'scope': 'finite diagnostic only', 'tables': report}, indent=2))
