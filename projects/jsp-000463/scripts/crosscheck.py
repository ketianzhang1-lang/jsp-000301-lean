"""Independent finite checks, supplementary to the general Lean proof."""
from itertools import combinations, product
import json


def check(modulus):
    points = list(product(range(modulus), repeat=2))
    lines = points.copy()
    point_neighbors = [{i for i, (a, b) in enumerate(lines)
                        if (y - a*x - b) % modulus == 0}
                       for x, y in points]
    line_degrees = [sum(j in ns for ns in point_neighbors) for j in range(len(lines))]
    edges = sum(map(len, point_neighbors))
    max_common = max(len(a & b) for a, b in combinations(point_neighbors, 2))
    assert all(len(ns) == modulus for ns in point_neighbors)
    assert all(d == modulus for d in line_degrees)
    assert edges == modulus**3
    assert 8*edges**2 == (2*modulus**2)**3
    return dict(modulus=modulus, vertices=2*modulus**2, edges=edges,
                regular_degree=modulus, max_common_neighbors=max_common)


records = [check(p) for p in (2, 3, 5, 7, 11)]
assert all(r['max_common_neighbors'] == 1 for r in records)
# The field hypothesis matters: Z/4Z has zero divisors and gives 4-cycles.
negative = check(4)
assert negative['max_common_neighbors'] > 1
print(json.dumps(dict(prime_checks=records, composite_negative_control=negative), indent=2))
