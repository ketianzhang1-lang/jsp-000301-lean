# Original statement correspondence

JSP-000725 is Erdős problem 874: the largest size of an admissible subset of
`{1,…,N}`, where equal sums of distinct elements cannot use different numbers
of summands. Theorem 1, page 142, of
[Deshouillers–Freiman (1999)](https://www.numdam.org/article/AST_1999__258__141_0.pdf)
proves the matching upper bound for sufficiently large `N`. Straus's terminal
interval supplies the lower construction. The resulting maximum is eventually
`floor(sqrt(4*N+1)) - 1`, and its ratio to `sqrt(N)` tends to 2.

| Original object or result | Lean correspondence |
| --- | --- |
| Finite sets of positive integers bounded by `N` | `A : Finset ℕ` with `A ⊆ Finset.Icc 1 N`. |
| Distinct summands | Subsets of a `Finset`, so no repeated elements occur. |
| Equal sums determine the number of summands | `JSP000725.Admissible A`. Both subsets may be empty and may overlap. |
| Integer restricted-sumset formulation | `admissible_iff_upstream` proves equivalence for positive sets. `boundedAdmissible_iff` includes the ambient interval. |
| No loss from changing ℕ to ℤ | `card_toInt`, `sum_toInt`, and `exists_nat_preimage` establish a cardinality-preserving correspondence in both directions. |
| The full extremal problem | `admissibleFamily N` filters the entire powerset of `{1,…,N}`; `maxCard N` is its maximum cardinality. `maxCard_eq_upstream` identifies it with `Erdos874.k N`. |
| All-`N` explicit lower witness | `terminalInterval_spec`, using our original `interval_admissible` and `interval_card`. |
| Eventual exact maximum | `eventual_maxCard_exact`. |
| Optimality against arbitrary admissible sets | `eventual_terminalInterval_optimal`. The quantified competing set is unrestricted within the original ambient interval. |
| Sharp asymptotic constant | `maxCard_asymptotic`. |
| Combined complete endpoint | `JSP000725.jsp_000725`. |

The imported predicate uses only positive-cardinality restricted sumsets. Our
predicate also allows empty subsets. Positive ambient elements make the sum of
any nonempty subset strictly positive; the proved bridge handles this distinction
instead of adding a hypothesis to the final theorem.

The final endpoint has no structural, density, or upper-bound assumption. The
imported `erdos_874_eventual_exact` proves the needed structural inputs within
its pinned transitive proof closure. Its full dependencies are included in the
axiom audit and independent-checker export.

The all-`N` quantifier applies to the construction. The maximum-cardinality
formula and optimality apply for all sufficiently large `N`. No explicit onset
threshold, classification of all maximizers, or all-small-`N` exact formula is
claimed. These stronger statements are not needed for the original asymptotic
question or the eventual exact resolution.
