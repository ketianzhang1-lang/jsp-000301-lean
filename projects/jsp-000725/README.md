# JSP-000725: the classical consecutive-interval construction

This package formalizes a **scoped component**, not the full eventual extremal
theorem for arbitrary sets. The mathematical construction is historical, not new.

For a finite set A of positive integers, admissibility means that any two subsets
with equal sums have equal cardinalities. Subsets have distinct elements; the
empty subset is permitted.

## Proven statements

- For every natural N and m with m <= N and (m+1)^2 <= 4N+1, the interval
  {N-m+1, ..., N} is admissible and has exactly m elements.
- For **every** N, including zero, there is an admissible subset of {1,...,N}
  with exactly floor(sqrt(4N+1))-1 elements. `Nat.sqrt` is the integer square root.
- In particular, for every t there is a 2t-element admissible subset of
  {1,...,t^2+t}.
- For every t >= 2, the 2t-element interval
  {t^2-t,...,t^2+t-1} is **not** admissible. The t-1 largest elements
  {t^2+1,...,t^2+t-1} and the t smallest elements
  {t^2-t,...,t^2-1} have equal sums.

The last theorem shows the even-length sufficient endpoint cannot be lowered
uniformly by one. It is not a proof of necessity for every possible interval.
We do not prove the optimal upper bound for arbitrary admissible sets, the full
large-N theorem, or any new result in number theory.

## Proof outline and source correspondence

`sum_lower` and `sum_upper` prove the usual bounds for sums of k distinct
integers in an interval, by induction on the least or greatest element.
`interval_ordered_sums` shows that any smaller-cardinality subset has a strictly
smaller sum under the stated quadratic condition. Its arithmetic step uses the
nonnegativity of (2k+1-m)^2. The construction and boundary statements follow.

The precise source is Deshouillers and Freiman (1999), page 141, which attributes
this consecutive-interval calculation to E. G. Straus (1966). Their full
Theorem 1 on page 142 is **not** included here. Erdős introduced admissibility
in 1962, according to the same paper.

- [Official JSP-000725 record](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000725)
- [Deshouillers and Freiman, On an additive problem of Erdős and Straus, 2](https://www.numdam.org/item/AST_1999__258__141_0/)
- [Original paper, pages 141-148](https://www.numdam.org/article/AST_1999__258__141_0.pdf)
- Straus, E. G., On a problem in combinatorial number theory, J. Math. Sci. 1
  (1966), 77-80. This attribution was checked in the 1999 paper; the 1966 paper
  itself was not independently consulted.

The Lean implementation was independently written with OpenAI ChatGPT
assistance under the submitting account's direction. Mathlib supplies standard
infrastructure and tactics. No third-party solution file is copied. A search of
official public issues and PRs for JSP-000725 found no matching submission at
the time of preparation; this is not a guarantee of global priority.

## Reproduction

The project pins Lean 4.34.0 and Mathlib v4.34.0, with transitive dependencies
locked in lake-manifest.json. In this directory:

```sh
lake exe cache get
lake build --wfail
lake env leanchecker --verbose JSP000725
lake env lean -DwarningAsError=true Audit.lean > axioms.log
python3 audit.py axioms.log
```

The GitHub workflow additionally requires rejection of the false statement
`(1 : Nat) = 0`. This is an independent negative control, not part of the proof.
The axiom audit covers all ten proved declarations. No `sorry`, custom axiom,
native-evaluation proof, or unsafe theorem-producing code is used.

Cached dependencies and network access are used. `leanchecker` replays the target module against the imported, pinned Mathlib
environment using Lean's own kernel. It does not replay the whole dependency
library from an empty environment and is not an independently implemented checker.
These are contributor-run checks. Independent statement review, formalization
eligibility, contribution assessment and any award decision remain outstanding.

Proposed contributor placeholder: RECIPIENT-JSP-000725-KZ-A, confirmation pending.
No amount, award, payment entitlement or first-formalization priority is claimed.
