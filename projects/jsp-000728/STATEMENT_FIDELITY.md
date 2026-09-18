# Original question and formal statement correspondence

The catalog entry JSP-000728 concerns inclusion-maximal sum-free subsets of
`{1,…,N}` (Erdős problem 877). Section 1, page 2 of
[arXiv:1409.5661](https://arxiv.org/pdf/1409.5661) records the original question:
whether maximal sets are negligible compared with all sum-free sets, or even
exponentially fewer. It records the affirmative result of Łuczak and Schoen.
The paper then proves a stronger sharp exponential scale. These are distinct
statements; our completeness claim concerns the original relative-count
question, including its stronger exponential-separation form.

| Mathematical object or assertion | Lean declaration / correspondence |
| --- | --- |
| Sum-free finite set, allowing equal summands | `JSP000728.SumFree`; `sumFree_iff_upstream` proves equivalence with `Erdos877.SumFree`. |
| Inclusion-maximal within the entire interval | `JSP000728.MaximalSumFree`; `maximalSumFree_iff_upstream` handles both interval containment and the equality direction. |
| Number of all maximal sets | `(JSP000728.maximalSets N).card`; `maximalSets_card_eq_upstream` proves equality with `Erdos877.maximalSumFreeCount N`. |
| Number of all sum-free sets | `(JSP000728.allSumFreeSets N).card`; `allSumFreeSets_eq_upstream` proves equality of the actual finite families. |
| All-interval lower bound | `cameron_erdos_lower_bound`; `N/4` here is natural-number division. |
| Benchmark lower bound for all sets | `upperHalf_powerset_subset`, `allSumFreeSets_lower_bound`, `benchmark_le_allSumFreeSets`. The finite interval has `N-N/2 = ceil(N/2)` elements. |
| Little-o against `2^(N/2)` | `maximalCount_isLittleO_benchmark`; exponent division is in the reals. |
| Negligibility relative to all sets | `maximalCount_isLittleO_allCount`, `maximal_to_all_ratio_tendsto_zero`. |
| Fixed exponential separation | `relative_exponential_saving` with the witness `δ = 1/2 - Erdos877.resolutionExponent > 0`. |
| Combined original-question endpoint | `JSP000728.jsp_000728`. |

Every counting definition enumerates a complete finite powerset and filters by
the stated property. Neither the maximal family nor the set of permissible
summands is restricted to our constructed examples. The upper-half construction
is only an injection proving a lower bound for the number of all sum-free sets.

The imported exponent is proved less than `1/2`. Multiplying its eventual
upper bound by `2^(δN)` gives `2^(N/2)`, which is at most `F(N)` by our injection.
Division by the strictly positive exponential proves the relative saving.
No unproved counting hypothesis, `sorry`, `admit` or custom axiom supplies a
missing step. The axiom audit checks the complete final theorem closures.

We do not establish `M(N) = 2^((1/4+o(1))N)`, a sharp constant on each residue
class, an explicit optimal onset threshold, or a new mathematical solution.
The full original comparison follows without any of those later refinements.
