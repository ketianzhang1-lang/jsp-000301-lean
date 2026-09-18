# Original-statement correspondence — JSP-000636 / Erdős 776

## Authoritative question used for scope

[He and Tang, arXiv:2602.09803v1, Problem 1.1](https://arxiv.org/html/2602.09803v1#S1)
reproduces the Erdős–Trotter question from the original references. It asks
for estimates of the eventual threshold for antichains with exactly r members
at each occurring size. Definition 1.3 identifies n₀(r) as the least integer
cutoff for which g(n,r)=n−3 whenever n>n₀(r).

The question asks for **estimates**, not a piecewise exact formula or a formula
for every g(n,r) below the eventual threshold. We interpret a proved all-parameter
two-sided estimate with the sharp leading asymptotic as an answer to that
original request. Maintainers must review this scope correspondence; repository
validation by itself does not adjudicate it.

## Correspondence table

| Original object or condition | Submitted formal object or theorem |
| --- | --- |
| Arbitrary ground set of cardinality n | Any `α : Type u` with `Fintype α`; n=`Fintype.card α`. A finite subset of another type is represented by its subtype. |
| Distinct subsets | `F : Finset (Finset α)`; the two finite-set levels exclude duplicates. |
| No distinct member contains another | Mathlib `IsAntichain (· ⊆ ·) (↑F : Set (Finset α))`. |
| Exactly r subsets at each occurring size | `ExactMultiplicityOn r F`, using the cardinality of the actual filtered family. |
| All multiplicities r>1 | Every natural r≥2, with no upper bound on r. |
| All sufficiently large n | Explicit N=2r+4⌊√r⌋+7, and every finite α with N<card α. |
| r(n−3) members are attainable | `finite_type_attaining_family`; first half of `original_threshold_question`. |
| r(n−2) members are impossible | Universal upper bound `finite_type_card_le`; second half of `original_threshold_question`. |
| Genuine least cutoff n₀(r) | `threshold_exact_spec` for `exactExtremal`; minima are established by the earlier threshold existence proof. |
| Threshold estimates | `threshold_bounds`, `threshold_relative_bound`, and `threshold_ratio_tendsto`. |
| Complete combined endpoint | `JSP000636.jsp_000636` in `OriginalQuestion.lean`. |

The generalized exact-multiplicity predicate reduces to `ExactMultiplicity` on
`Fin n`. `mapFamily` uses injective maps twice, preserving subset sizes, family
size and every occurring-level multiplicity. `mapFamily_antichain_iff` proves
containment correspondence. Thus the passage between `Fin n` and an arbitrary
finite ground set is proved, rather than assumed.

For r≥2, the exhibited cutoff ensures n≥4, so truncated natural-number
subtraction cannot create vacuous negative-size cases. The r=1 observation in
the question is background; the threshold-estimate request concerns r>1.

## Limits, stronger results and prior work

The proof covers the original threshold-estimate request. It does not prove
the source paper's sharper logarithmic error term or exact values at r=2,3,
and does not prove the stronger exact formula advertised by PR #677.
The bounds nevertheless hold for every parameter in their stated domains,
and the existence/impossibility statement covers every r≥2.

These distinctions also explain the revision of our earlier partial-scope
assessment: lack of the stronger exact formula is not, by itself, a missing
case of the original estimate question. Prior formalization and contribution
eligibility must still be assessed separately from theorem completeness.
