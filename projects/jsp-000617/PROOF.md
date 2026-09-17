# Proof of the upper-density variant

This is an exposition of the construction formalized here, with mathematical
attribution to Bhalla and Tao as described in README.md.

Fix m and write k=2^m≥4. We construct A with upper sumset density at least 1−3/k
and a uniform ordered representation bound

C_m = 8k²(m+1)² + 24k(m+1).

## 1. Finite planes

In an odd-characteristic finite field, equality of x+y and x²+y² determines the
unordered pair {x,y}. Thus a point has at most two ordered representations as a
sum of two points on the parabola (x,x²). Its sumset covers at least half the plane.

Averaging translates of this sumset successively halves the uncovered set. A union
of at most m+1 translates of the parabola consequently has sumset covering at
least 1−1/k of the plane. Its representation bound is 2(m+1)². Each horizontal
row contains at most 2(m+1) points, because each translated quadratic has at most
two roots in that row.

Implemented in JSP000617, JSP000617Cover, and JSP000617Sparse.

## 2. Ordinary natural-number packets

For a prime p>2, encode (x,y)∈F_p² by val(x)+2p val(y). Equality of ordinary
integer sums determines equality of the finite-field coordinate sums. Adjacent
copies shifted by p control the first-coordinate carry and cover both half-row
positions modulo M=2p². This gives a block inside [0,M) with at least
(1−1/k)M covered residues, representation bound 8(m+1)², and at most 12(m+1)
points in any subset of diameter at most p.

Repeat that block k times, with spacing M. For each covered residue, a witnessing
sum z generates the 2k−1 distinct ordinary sums z+jM, 0≤j≤2k−2. Their values lie
inside [0,2kM); equality between two such sums forces both the residue and j to
agree. We obtain Q⊆[0,L), L=kM, satisfying

k |Q+Q| ≥ (k−2) 2L,

r_Q(n) ≤ R_m := 8k²(m+1)²,

and at most S_m := 12k(m+1) points in each subset of diameter at most p.

Implemented in JSP000617Nat, JSP000617Lift, and JSP000617Packet. All additions in
these packet statements are ordinary natural-number additions, not modular sums.

## 3. Extending a finite stage

Let B be the already constructed finite stage, with max B≤d and representation
bound C_m=R_m+2S_m. Put t=2d+1. Choose an arbitrarily large prime p≥t+j+3, where j
is a requested lower bound for the next density witness. Construct Q as above,
and adjoin T=t+Q.

For n<t, no pair using T can sum to n, so the old bound is unchanged. For n≥t,
no old-old pair sums to n, since its sum is at most 2d<t. New-new pairs contribute
at most R_m. For old-new pairs, the new summands lie in a set of diameter at most
d≤p, and hence there are at most S_m. The same bound holds in reverse order.
Thus B∪T has representation bound C_m for all n, with no accumulation over stages.

Set N=2(t+L). All of T+T lies below N. Since p≥t and L=2kp², we have
(k−3)t≤L, whence

(k−3)N ≤ (k−2)2L ≤ k|T+T|.

Thus the enlarged stage has sumset prefix density at least 1−3/k at some positive
N≥j. Implemented in JSP000617Gluing and JSP000617Stages.

## 4. Infinite union and limsup

Iterate the extension and take the increasing union A of the finite stages.
For fixed n, the finite set A∩[0,n] lies in a single stage. Consequently every
ordered representation of n lies in that stage and r_A(n)≤C_m.

Every finite-stage sum is also in A+A. The construction therefore supplies,
for every j, some N≥j with N>0 and

| (A+A) ∩ [0,N) | / N ≥ 1−3/k.

The prefix densities are bounded above by 1, so their limsup is at least 1−3/k.
Finally choose m with 2^m>max(4,3/ε). This proves the stated upper-density theorem.
Implemented in JSP000617Upper.

This argument supplies arbitrarily large good prefixes. It does not assert that
all sufficiently large prefixes have the same lower bound, which would be the
original lower-density question.
