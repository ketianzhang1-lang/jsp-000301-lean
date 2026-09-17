# JSP-000154 / Erdős Problem 156: elementary lower bound

This package formalizes a known lower-bound component. It does **not** solve the open existence question for an inclusion-maximal Sidon set of size O(N^(1/3)), prove Ruzsa's upper bound, or claim new mathematics or global first-formalization priority.

## Exact scope
For every natural N, including zero, and every inclusion-maximal Sidon subset A of {1,...,N}, with m = |A|, Lean proves:

- 2*N <= m^3 + m.
- N^(1/3) <= m and (2*N)^(1/3) <= m+1 over the reals.
- Existence of such sets, attainment of the minimum size, and the same bounds for that actual minimum.
- The one-element extension definition is equivalent to inclusion-maximality among all Sidon subsets of the interval.

Repeated summands are included in the Sidon condition: a+b=c+d permits only the two orderings of the same pair. This is not the weaker distinct-summand convention. Maximal means inclusion-maximal, not maximum cardinality.

## Proof
For each x outside A, inserting x violates the Sidon condition. After removing cancellations and interchanging a,b, the violation has one of two forms:

1. 2*x=a+b, with a<b in A.
2. x+c=a+b, with c in A, a,b in A\{c}, and a<=b.

There are at most m*(m-1)/2 candidates of the first kind and m^2*(m-1)/2 candidates of the second kind. Every interval element belongs to A or to these candidate sets. Thus N <= m + m*(m-1)/2 + m^2*(m-1)/2 = (m^3+m)/2. Candidate values outside the interval and repeated representations only enlarge the upper count; no injectivity is assumed. The Lean proof handles natural subtraction and the empty interval explicitly.

## Reproduce
Use the committed Lean 4.34.0 toolchain and lockfile:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

See VERIFICATION.md for which checks were actually run. The scripts include a separate NaNoda implementation and an axiom allowlist. Cached Mathlib is used; this is not a clean offline rebuild.

## Attribution and review
Original problem and classical background: Erdős, Sárközy and Sós, *On Sum Sets of Sidon Sets, I*, Journal of Number Theory (1994), 329–347. Ruzsa, *A small maximal Sidon set*, Ramanujan Journal (1998), 55–58, concerns the stronger upper-bound direction, which is not proved here.

Sources and statement comparison:
- [Organizer catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000154).
- [Erdős Problem 156](https://www.erdosproblems.com/156).
- [Formal Conjectures statement snapshot](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/156.lean).

The Formal Conjectures snapshot records the open upper-bound question and known lower-bound direction. It was consulted for scope; it is not imported, and its unproved declarations are not dependencies. This independent Lean implementation continues the submitting account's prior work with OpenAI ChatGPT assistance. Mathlib and Lean retain their respective credits and licenses. The displayed finite polynomial inequality is an explicit counting form of the elementary lower-bound argument; no novelty is asserted for its constant.

On the checked catalog snapshot the whole problem is Open / Lean proof No / Eligible to claim No. Please assess whether this scoped formalization qualifies for contribution review. No catalog, candidate, award or recipient-confirmation record is changed. Proposed contributor: RECIPIENT-JSP-000154-KZ-A, confirmation pending; submitting account ketianzhang1-lang. No payout or organizer approval is claimed.
