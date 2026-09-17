# JSP-000250: prime denominator obstruction and upper bound

This project formalizes the **upper-bound half** of Liu and Sawhney,
*On further questions regarding unit fractions* (2024), Theorem 1.6, Section 4.
It is a contribution for review, not a complete formalization of that theorem:
the near-matching lower bound is not included. No new mathematical discovery,
global first-formalization priority, award, or entitlement to payment is claimed.

## Statement and coverage

`Representable N t` means that `t` is positive and that a finite set of distinct
positive integer denominators, all between `t` and `N`, contains `t` and has
reciprocal sum exactly one. The use of rational arithmetic expresses the exact
equality; finite rational sums have the same equality after embedding in the reals.

`firstException N` is the least positive `t` for which that representation is
impossible. Existence follows since `N+1` is outside the permitted denominator
range. Its specification and the representability of every smaller positive
integer are proved, not assumed. The definition also handles `N=0`.

The main results are:

- `prime_not_representable`: for every prime `p` and naturals `N,m`, if
  `N <= p*m` and `m*lcm(1,...,m) < p`, then `p` cannot be the least denominator.
- `prime_exception_upper_bound`: for every positive natural `N` with
  `log N >= 128`, there is a prime `p <= N` which is not representable and
  satisfies `p <= 128*N/log N`.
- `firstException_upper_bound`: the same explicit bound for the least exception.
- `firstException_isBigO`: the unconditional asymptotic theorem
  `t(N) = O(N/log N)` along all natural `N` tending to infinity.

The constant and threshold are deliberately loose. This proves the upper-bound
order from the paper; it does not claim its displayed constant 10 or the lower
bound, an exact computation of `t(N)` for all `N`, or completion of the catalog
problem. No extra mathematical hypothesis is assumed in the asymptotic theorem.

## Proof outline

Separate denominators divisible by `p` from the others. Divide the former by
`p`, and let `L=lcm(1,...,m)`. Clearing denominators forces `p` to divide the
positive integer `A=sum L/k`, while distinctness and `k<=m` give `A<=m*L<p`.
This is impossible. Mathlib's Chebyshev estimate bounds `log(m*L)` by `8m`.
Bertrand's postulate supplies a suitable prime near `64N/log N`, giving the
explicit bound and then the asymptotic statement.

## Sources and attribution

- [Official JSP-000250 catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000250).
- [Liu and Sawhney, arXiv:2404.07113v1](https://arxiv.org/html/2404.07113v1#S4),
  Theorem 1.6 and its upper-bound proof. The paper credits the upper bound to
  Erdős and Graham, *Old and new problems and results in combinatorial number
  theory* (1980), page 35, and discusses earlier related work.
- Mathlib supplies the established Chebyshev and Bertrand theorems and other
  infrastructure; their authors retain credit. See the pinned dependency manifest.

This Lean implementation was prepared with OpenAI ChatGPT assistance under the
submitting account's direction. Mathematical discovery remains with the cited
authors. Proposed formalization recipient: `RECIPIENT-JSP-000250-KZ-A`, pending
confirmation. The submitting account has an interest in the eligibility review.

## Reproduction

Use the exact Lean 4.34.0 toolchain and dependencies in `lake-manifest.json`:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The scripts build with warnings as errors, replay the module in the bundled
checker, audit eight declarations against the three standard axioms, reject a
false-arithmetic negative control, and export the target dependency closure for
the independently implemented NaNoda checker with a strict axiom allowlist.

Actual run details belong in the submission verification receipt. A script's
presence alone is not evidence that it ran. Cached Mathlib and network access are
used; no offline rebuild of the entire library or independent human certification
is claimed. Contributor-run checks do not establish organizer approval.
