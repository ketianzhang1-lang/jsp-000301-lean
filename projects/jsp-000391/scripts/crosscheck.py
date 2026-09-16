"""Independent exact rational sanity checks, not a Lean proof dependency."""
from fractions import Fraction as Q
from math import floor

cases = 0
for g in range(2, 12):
    low = -Q(1, g)
    high = Q((g+1)*(g-2), g)
    for j in range(10):
        t = Q(1) + Q(j*(g-1), 10)
        for shift in (low, (low+high)/2, high - (high-low)/100):
            a = Q(g) / ((g-1)*(t+g))
            b = Q(g) / a
            u = [1]
            for n in range(40):
                u.append(floor(a*(u[-1]+shift)) if n%2 == 0
                         else floor(b*(u[-1]+Q(1,g-1))))
            for n in range(20):
                expected = floor(t) if n == 0 else floor(t*g**n)-g*floor(t*g**(n-1))
                actual = u[2*n+2] - g*u[2*n]
                assert actual == expected, (g,t,shift,n,actual,expected)
                assert 0 <= actual < g
            cases += 1
print(f'PASS: {cases} exact rational parameter triples; {cases*20} digits.')
print('Finite diagnostic only; universal correctness is established by the Lean theorem.')
