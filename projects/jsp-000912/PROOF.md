# A multiscale construction for JSP-000912 / Erdős 1099

## Status and attribution

This mathematical proof was prepared on 2026-09-17. Its full main statement and all construction lemmas have now been implemented and successfully compiled in Lean 4.19.0, then mechanically ported and checked in Lean 4.34.0 with pinned Mathlib; the transitive axiom audit reports only propext, Classical.choice, and Quot.sound. This is not an award decision or independent referee report. The affirmative mathematical answer to Erdos 1099 is due to Michael D. Vose (1984). The construction and implementation below were developed during this session. A later global code search found a pre-existing public full formalization in plby/lean-proofs, at revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Accordingly, NO first-formalization priority or award eligibility is asserted. See README.md for the precise source and verification limitations.

The original question is the full statement, for every real alpha > 1, that the lower limit as n tends to infinity of the consecutive-divisor ratio-power sum is finite. The factorial and least-common-multiple variants are separate questions and are not claimed here.

## Statement

For a positive integer n with positive divisors

    1 = d_1 < ... < d_s = n,

put

    h_alpha(n) = sum_{j=1}^{s-1} (d_{j+1}/d_j - 1)^alpha.

**Theorem.** Let alpha > 1, and choose a positive integer r with

    r (alpha - 1) >= 4.

Write c = r(r+1), and for integers K >= 1 define

    Q_i = product_{j=1}^r [2^(ij) (2^(ij)+1)]^(2^(i+1)),
    P_K = product_{i=1}^K Q_i,
    E_K = 16 c (K+1) 2^K,
    N_K = 2^(E_K) P_K.

Then N_K tends to infinity and

    h_alpha(N_K) <= 64 [16r(r+1)+2]^2

for every K >= 1. In particular, the theorem answers the full main question, not just the alpha >= 2 subcase.

## 1. A finite mixed-radix approximation lemma

Fix integers m >= 2 and r >= 1, and put M = 2m,

    A = product_{j=1}^r (m^j)^M = m^[m r(r+1)],
    Q = product_{j=1}^r [m^j (m^j+1)]^M,
    rho_j = 1 + m^(-j),   0 <= j <= r.

Thus rho_0 = 2. Bernoulli's inequality gives, for j >= 1,

    rho_j^m >= 1 + m m^(-j) = rho_{j-1}.

For any 1 <= y < 2 construct integers k_j greedily. Begin with remainder y_0 = y. Given 1 <= y_{j-1} < rho_{j-1}, choose the unique integer k_j >= 0 satisfying

    rho_j^k_j <= y_{j-1} < rho_j^(k_j+1),

and let y_j = y_{j-1}/rho_j^k_j. Since y_{j-1} < rho_j^m, necessarily 0 <= k_j < m <= M. After r steps,

    1 <= y / product_j rho_j^k_j < rho_r.

The positive integer

    p = product_{j=1}^r (m^j)^(M-k_j) (m^j+1)^k_j

divides Q. Also p/A = product_j rho_j^k_j, so

    p <= A y < (1+m^(-r)) p.                         (1)

No density assumption, limiting equidistribution theorem, or assertion about prime gaps is used.

More generally, suppose 2^E Q divides an integer n. If

    A <= x <= 2^E,

write x/A = 2^q y, with q a nonnegative integer and 1 <= y < 2. Since A >= 1, one has q <= E. Multiplying (1) by 2^q gives a divisor d = 2^q p of n with

    d <= x < (1+m^(-r)) d.                          (2)

This argument works even when Q itself contains powers of two: divisibility follows by multiplying the two explicitly available factors, not by assuming they are coprime.

## 2. Size of the constructed integers

For i >= 1, put m = 2^i. Since 2^(ij)+1 <= 2^(ij+1),

    log_2 Q_i <= sum_{j=1}^r 2m(2ij+1)
               = 2m [i r(r+1)+r]
               <= 4 c i 2^i.

Here r <= i r(r+1). Hence

    log_2 P_K <= 4c sum_{i=1}^K i2^i
               <= 4c K sum_{i=1}^K 2^i
               < 8c K2^K
               <= E_K.

Consequently

    P_K <= 2^(E_K),  N_K <= 2^(2E_K).

Let T = 2^(E_K). Every power 2^q with 0 <= q <= E_K divides N_K. In particular, consecutive divisors a < b with b <= T have b/a <= 2: otherwise a power of two would lie strictly between them.

The denominator baseline of the grid at level i is

    A_i = 2^[c i2^i].

By (2), whenever 1 <= i <= K and A_i <= x <= T there is d | N_K with

    d <= x < (1+2^(-ri)) d.                         (3)

## 3. A grid bounds actual consecutive-divisor gaps

Let a < b be consecutive divisors of N_K with b <= T and a >= A_i. Then

    b/a - 1 <= 2^(-ri).                             (4)

Indeed, if b > (1+epsilon)a, with epsilon = 2^(-ri), choose

    x = [b + (1+epsilon)a]/2.

Then A_i <= a < x < b <= T and x > (1+epsilon)a. Equation (3) supplies a divisor d with d <= x < b and d > x/(1+epsilon) > a, contradicting consecutiveness.

This verifies the transition from the constructed grid to all actual divisors, including additional divisors not explicitly used by the construction.

## 4. A uniform weighted gap estimate

Set

    beta = alpha-1 > 0,
    B = 16c+2,
    g = b/a-1,
    t = 1+log b,

where log is the natural logarithm and a < b are consecutive divisors with b <= T. We have 0 < g <= 1 and t >= 1. Because log 2 < 1 and K+1 <= 2^K,

    t <= 1+E_K log 2
       <= 1+16c(K+1)2^K
       <= B 4^K.                                   (5)

For every 1 <= i <= K, the condition B4^i < t implies a >= A_i. In fact, b <= 2a gives

    log a >= log b - log 2 = t-1-log 2
          > B4^i-2
          >= c4^i
          >= c i2^i log 2
          = log A_i,

using i <= 2^i. Thus (4) applies whenever B4^i < t. For i=0 the analogous gap estimate g <= 2^0 = 1 already holds.

If t <= B, then g^beta t^2 <= B^2. Otherwise, by (5), some integer 0 <= i < K satisfies

    B4^i < t <= B4^(i+1).

For that i,

    g^beta t^2
       <= 2^(-ri beta) B^2 16^(i+1)
       <= 16 B^2,                                  (6)

since r beta >= 4. This argument uses the entire range alpha > 1; increasing r compensates for beta being arbitrarily small.

## 5. Telescoping potential; both halves of the divisor list

For x >= 1 define

    W(x) = 1/(1+log x),    C = 16B^2.

For 0 <= g <= 1,

    log(1+g) >= g/(1+g) >= g/2.

Also,

    W(a)-W(b)
      = log(b/a)/[(1+log a)(1+log b)]
      >= g/[2(1+log b)^2].

Combining this with (6) yields

    g^alpha <= 2C [W(a)-W(b)]                       (7)

for every consecutive pair with b <= T.

If b > T, consecutiveness and T | N_K imply a >= T. The reflected pair

    a' = N_K/b < b' = N_K/a

is again a consecutive pair of integer divisors. Its upper endpoint is at most N_K/T = P_K <= T, and b'/a' = b/a. Therefore (7) gives

    g^alpha <= 2C [W(N_K/b)-W(N_K/a)].              (8)

Both differences on the right sides of (7) and (8) are nonnegative. Thus every consecutive pair, in either half of the divisor list, satisfies

    g^alpha <= 2C {W(a)-W(b)+W(N_K/b)-W(N_K/a)}.

Summing over the complete sorted divisor list telescopes both differences:

    h_alpha(N_K)
       <= 4C [W(1)-W(N_K)]
       <= 4C
       = 64[16r(r+1)+2]^2.

This includes a pair adjacent to T and needs no omission or separate unbounded estimate for a central gap.

Finally, E_K >= K and N_K >= 2^K, so the integers N_K are unbounded. The asserted lower-limit bound follows.

## 6. The related unpowered ratio question (informal corollary)

Sections 1–5 are implemented in the audited Lean theorem. The short supplementary corollary in this section is a mathematical deduction and is not separately exported by the supplied Lean files.

For every u >= 0, u-log(1+u) <= u^2. Hence, for any positive integer n,

    sum_j d_{j+1}/d_j - tau(n) - log n
      = sum_j [g_j-log(1+g_j)] - 1
      <= h_2(n)-1.

Taking alpha=2 in the construction proves finiteness of the lower limit in this supplementary question as well. This is a consequence of the full main theorem, not a substitute for it.

## Sources and scope record

- Official catalog: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000912
- Original-problem transcription: https://www.erdosproblems.com/1099 and https://www.erdosproblems.com/latex/1099
- P. Erdos, Some problems and results on additive and multiplicative number theory, Lecture Notes in Mathematics 899 (1981), 171-182, especially p.171.
- M. D. Vose, Integers with consecutive divisors in small ratio, Journal of Number Theory 19 (1984), 233-238. DOI: 10.1016/0022-314X(84)90107-0.

The theorem above is an affirmative proof of the already-known main mathematical result. It does not settle the factorial or lcm variants, and no such claim is necessary to the main existence question. The full main theorem now has a compiled, audited implementation in this package. However, the later discovery of a pre-existing full formalization prevents any first-formalization claim. No organizer acceptance or award decision is asserted.
