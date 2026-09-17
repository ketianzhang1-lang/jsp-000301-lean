# JSP-000212: prime-power Bose--Chowla construction

For every prime p, positive integer r and integer h >= 2, put q=p^r.
This project proves that there exists a set A of exactly q positive integers
at most q^h-1 such that two sums of h elements of A that are congruent
modulo q^h-1 have equal multisets of summands. Repetitions are allowed.

The theorem `BoseChowlaPrimePower.exists_prime_power_modular` gives the
classical finite modular construction in full. The endpoint
`BoseChowlaPrimePower.jsp000212_prime_power` specializes to h=3 and the
catalog's distinct-three-element-subset condition. This remains a
**known lower-bound component** of the open extremal JSP-000212 problem.

## Supplement to the initial contribution

The initial version covered only prime cardinalities and equality in the
integers. This supplement removes both restrictions. The final theorem
constructs the required field extension and proves its dimension; it does
not take either fact as an unproved hypothesis.

BoseChowla.lean and Audit.lean are unchanged from initial proof commit
`5a44bae1b7d4a8a70d1f8594e26688f251f0b9e0`. PrimePower.lean and
PrimePowerAudit.lean contain the new proof and audit. This extends the
same contribution in [PR #423](https://github.com/TheJustinSunPrize/awards/pull/423),
not a separate award request.

## Proof

Embed the field of p^r elements in the field of p^(r*h) elements.
Mathlib's finite-field embedding theorem and the tower dimension formula
give extension degree h. Choose a primitive element theta for this
extension and a generator g of its multiplicative group. Every theta-a
for a in the base field is nonzero and has an exponent modulo q^h-1.

Congruent exponent sums give equal products of theta-a. Subtract the two
monic degree-h products of linear polynomials. Their leading terms cancel,
leaving degree below h. Vanishing at theta and its minimal-polynomial
degree force the difference to be zero, hence the multisets of roots agree.
Shifting exponents by one gives positive representatives and preserves
congruence for equal-cardinality sums.

## Attribution and scope

- [Official statement](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000212).
- R. C. Bose and S. Chowla, [Theorems in the additive theory of numbers](https://doi.org/10.1007/BF02566968), Commentarii Mathematici Helvetici 37 (1962/63), 141--147.
- Theorem 1 of the [authors' 1960 report](https://www.cs.umd.edu/~gasarch/COURSES/858/S13/BoseChowla.pdf) gives the classical prime-power modular construction.
- [Initial proof and provenance](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5a44bae1b7d4a8a70d1f8594e26688f251f0b9e0/projects/jsp-000212).

Mathematical credit belongs to Bose and Chowla. This independently written
Lean implementation was prepared with OpenAI ChatGPT assistance under the
direction of ketianzhang1-lang. Mathlib supplies the finite fields,
polynomials, cyclic groups and linear algebra. The project is Apache-2.0.

No all-integer-cardinality construction, sharp upper bound, full asymptotic
answer, new mathematical discovery, worldwide priority or award entitlement
is claimed. Bounded submission searches do not establish global priority.

## Reproduction

Lean 4.34.0 and all Git dependencies are locked. Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get Mathlib.FieldTheory.Finite.GaloisField Mathlib.FieldTheory.PrimitiveElement Mathlib.Algebra.Polynomial.Roots Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Four modules are built with warnings as errors and replayed by the bundled
Lean checker. Both audits check exact endpoint types and ten axiom closures.
Non-prime instances include q=4, 8 and 9, with both h=2 and h=3 covered.
Dependency revisions are checked and false arithmetic must be rejected.
The pinned NaNoda checker replays the initial and expanded endpoint
closures with only propext, Classical.choice and Quot.sound permitted.

These commands describe the procedure; actual successful-run receipts
are recorded in the submission. Mathlib compiled caches are used; no
complete Mathlib source rebuild or independent human review is asserted.
Eligibility, recipient confirmation and any award require organizer review.
