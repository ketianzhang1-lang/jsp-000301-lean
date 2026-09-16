"""Finite exact-integer diagnostics, not a dependency of the universal Lean proof."""
from math import prod
SEED=734110615000775
MODULUS=36893488147419103230
assert MODULUS==2*3*5*17*257*65537*641*6700417
PRIMES=(3,5,17,257,65537,641,6700417)
def divisor(r):
    if r%2==1: return 3
    if r%8==4: return 17
    if r%16==8: return 257
    if r%32==16: return 65537
    if r==32: return 641
    return 6700417
for r in range(64):
    if r%4!=2:
        p=divisor(r)
        assert 1<p<=6700417 and pow(2,64,p)==1 and MODULUS%p==0
        assert (pow(SEED,4,p)*pow(2,r,p)+1)%p==0
count=0
for j in range(20):
    t=SEED+MODULUS*j
    k=t**4
    assert k>0 and k%2==1
    for n in range(513):
        value=k*2**n+1
        if n%4==2:
            x=t*2**(n//4)
            d=2*x*x-2*x+1
            assert value==d*(2*x*x+2*x+1)
        else:
            d=divisor(n%64)
        assert 1<d<value and value%d==0,(j,n)
        count+=1
    assert all((4*k+1)%p!=0 for p in PRIMES)
print(f'PASS: {count} proper-divisor checks; 20 failures of the specified seven-prime cover.')
print('Finite diagnostics only; arbitrary parameters and exponents are handled by the Lean proof.')
