#!/usr/bin/env python3
"""Independent finite sanity check using a divisor sieve, not the Lean implementation."""
from math import gcd
for n in (270, 540, 810):
    sigma = [0] * (n + 1)
    for d in range(1, n + 1):
        for m in range(d, n + 1, d):
            sigma[m] += d
    exact = sum(sigma[a]+sigma[b] == sigma[a+b]
                for a in range(1, n) for b in range(1, n-a+1))
    witnesses = set()
    for k in range(n//270):
        for r in range(1, 90):
            if gcd(r, 6) == 1:
                t = 90*k+r
                witnesses.update(((t, 2*t), (2*t, t)))
        for r in range(1, 30):
            if gcd(r, 30) == 1:
                t = 30*k+r
                witnesses.update(((4*t, 5*t), (5*t, 4*t)))
    assert len(witnesses) == 76*(n//270)
    assert all(0<a and 0<b and a+b<=n and sigma[a]+sigma[b]==sigma[a+b]
               for a,b in witnesses)
    assert exact >= len(witnesses)
    print(f'N={n}: exact ordered count={exact}, distinct constructed witnesses={len(witnesses)}')
