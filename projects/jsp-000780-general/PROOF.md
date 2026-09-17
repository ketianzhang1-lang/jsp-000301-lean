# Construction and proof

Fix an integer r ≥ 6. A positive integer n is r-full if p^r divides n for
every prime divisor p of n. All gcd statements below are collective.

Put m=⌊r/2⌋−2 and C=2 binom(r,3). Split C into the m distinct positive
coefficients

    1,2,...,m−1, C−m(m−1)/2.

The last coefficient is larger than m. For example, the checked bound
r(r−1) ≤ C and m ≤ r−2 establish this with ample room.
Let A consist of the pairs (j,2 binom(r,j)) for odd 1≤j≤r, j≠3, and
of (3,c) for each of these split coefficients. Thus |A|=r−3,
all its coefficients lie between 1 and K=2^(r+1), and (1,2r)∈A.
Set

    B = product of c over (j,c)∈A,
    H = 2^r K + 2,
    q_t = B(H+t)+1,   X = q_t^r,   Y = B^r.

For each natural t define

    S_t = {(X−Y)^r} ∪ {c X^(r−j) Y^j : (j,c)∈A}.

1. **Sum.** Odd terms of the binomial expansion give
   (X+Y)^r=(X−Y)^r+Σ_{j odd}2 binom(r,j)X^(r−j)Y^j.
   Splitting the j=3 coefficient preserves this identity.
2. **Distinctness and positivity.** We have X>HY, hence X>KY,
   X>2^r K Y and X≥2Y. Terms with different exponents j are strictly
   ordered: for j<k the ratio of their monomial factors is
   (X/Y)^(k−j)>K, exceeding any opposing coefficient ratio. Terms with
   equal j have distinct coefficients. Each monomial is at most
   K X^(r−1)Y, whereas (X−Y)^r≥X^r/2^r>K X^(r−1)Y.
   Consequently S_t contains exactly 1+|A|=r−2 positive terms.
3. **Fullness.** The first term and the sum are r-th powers. In each
   monomial, a prime dividing X or Y has multiplicity at least r.
   A prime dividing c also divides B, so its multiplicity in Y^j is
   at least r since j≥1. Thus every summand is r-full.
4. **Gcd.** q_t≡1 (mod B), so gcd(X,Y)=1. Hence X−Y is coprime to
   both X and Y. Also 2r divides B and therefore divides Y. It follows
   that (X−Y)^r is coprime to the j=1 summand (2r)X^(r−1)Y.
   Both are in S_t, so the gcd of S_t is 1.
5. **Infinitude.** q_t strictly increases with t, and so does
   (q_t^r+B^r)^r=ΣS_t. Therefore both the sets and their totals take
   infinitely many distinct values.

All five steps, coefficient counting, and inequalities are proved in Lean
for arbitrary r≥6 and arbitrary natural t. No finite search is used to
justify the universal statement. The explicit large H favors simple bounds,
not small numerical examples.
