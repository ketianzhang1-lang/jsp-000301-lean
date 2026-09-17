"""Independent exact diagnostic; the Lean theorem is the proof certificate."""
from collections import Counter
from itertools import combinations
from math import comb
import json

A = [-20, -19, -15, -13, -11, -10, -8, -7, -6, -5, -3, -2, -1,
     0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 15, 18, 21]
B = sorted(-x for x in A)
assert len(A) == len(set(A)) == len(B) == len(set(B)) == 27
assert A != B and 21 in A and 21 not in B
ca = Counter(sum(t) for t in combinations(A, 3))
cb = Counter(sum(t) for t in combinations(B, 3))
assert ca == cb
assert sum(ca.values()) == comb(27, 3) == 2925
# A deliberately altered input must fail the same equality check.
altered = B.copy()
altered[-1] += 1
assert Counter(sum(t) for t in combinations(altered, 3)) != ca
print(json.dumps({"A": A, "B": B, "cardinality": 27,
  "triples_each": 2925, "distinct_sums": len(ca),
  "min_sum": min(ca), "max_sum": max(ca),
  "zero_multiplicity": ca[0], "equal_with_multiplicity": ca == cb,
  "altered_input_rejected": True}, indent=2))
