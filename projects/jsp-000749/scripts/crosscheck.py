"""Exact finite diagnostics only; not imported by the universal Lean proofs."""
from math import comb
from fractions import Fraction
from itertools import product

def choose(a: int, b: int) -> int:
    return comb(a, b) if b <= a else 0

majorities = 0
for n in range(2, 61):
    N = 2*n*n
    D, E = comb(n*n, n), comb(N, n)
    assert E <= 2**(n+1)*D
    p = Fraction(D, E)
    assert p >= Fraction(1, 2**(n+1))
    for k in range(N+1):
        mono = choose(k,n)+choose(N-k,n)
        assert D <= mono <= E
        majorities += 1
triangle = [{0,1},{1,2},{0,2}]
def proper(c: tuple[int,...], edges: list[set[int]]) -> bool:
    return all(len({c[v] for v in e}) >= 2 for e in edges)
assert not any(proper(c,triangle) for c in product(range(2),repeat=3))
assert proper((0,1,2),triangle)
assert proper((0,1),[{0,1}])
assert not proper((0,),[{0}])
print('PASS: 59 exact binomial-ratio bounds; '+str(majorities)+' colour-class-size checks.')
print('PASS: triangle, single-edge and singleton-edge semantic diagnostics.')
print('These are finite diagnostics; all-parameter correctness is proved in Lean.')
