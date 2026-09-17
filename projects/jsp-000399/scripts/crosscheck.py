from collections import Counter
from itertools import combinations
A = [20,28,32,34,35,67,70,71,73,77,85,103,105,106,109,110,112,117,118,120,124,148,156,160,162,163,195]
B = [5,37,38,40,44,52,76,80,82,83,88,90,91,94,95,97,115,123,127,129,130,133,165,166,168,172,180]
assert len(A) == len(B) == 27
assert len(set(A)) == len(set(B)) == 27
assert min(A) > 0 and min(B) > 0
assert set(A) != set(B)
ca = Counter(map(sum, combinations(A, 3)))
cb = Counter(map(sum, combinations(B, 3)))
assert ca == cb
assert sum(ca.values()) == sum(cb.values()) == 2925
print("27 distinct positive entries per set; different sets; all 2925 triple sums agree with multiplicities.")
