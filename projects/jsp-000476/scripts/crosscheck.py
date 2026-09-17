"""Independent finite checks; these are supplementary, not the general proof."""
from math import isqrt
import json


def squarefree_part(m):
    result, p = 1, 2
    while p * p <= m:
        exponent = 0
        while m % p == 0:
            m //= p
            exponent += 1
        if exponent % 2:
            result *= p
        p += 1
    return result * m


checked = 0
for m in range(1, 129):
    sums = {0}
    for k in range(13):
        if k:
            sums |= {s + m * k for s in sums}
        actual = all(isqrt(s) ** 2 != s for s in sums if s > 0)
        expected = k * (k + 1) // 2 < squarefree_part(m)
        assert actual == expected, (m, k, actual, expected)
        if m == squarefree_part(m) and not actual:
            assert m * m in sums, (m, k)
        checked += 1
print(json.dumps({'multiplier_range': [1, 128], 'k_range': [0, 12],
                  'cases': checked, 'result': 'passed'}, sort_keys=True))
