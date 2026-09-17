# Statement fidelity

The catalog entry JSP-000264 corresponds to Erdős Problem 318. This package
proves its positive-density existence part, not every statement on that page.

| Original notion | Formalization in this project |
| --- | --- |
| A set of natural numbers | `A : Set ℕ` |
| Ignore zero in reciprocal sums | `A \ {0}` |
| Signs +1 and -1 | `Set.range f ⊆ {1, -1}` with `f : ℕ → ℝ` |
| Nonconstant signs on the relevant set | The two composition inequalities in `P₁` |
| A finite nonempty zero-sum subset | `S : Finset ℕ`, `S.Nonempty`, `↑S ⊆ A \ {0}`, and `∑ n ∈ S, f n / n = 0` |
| Positive natural density | `∃ d : ℝ, 0 < d ∧ HasNaturalDensity A d` |
| Complete part-i endpoint | `positive_density_counterexample` |

The P₁ definition agrees verbatim in mathematical content with the pinned
Formal Conjectures definition. The reference defines natural density by
`((A ∩ univ) ∩ Iio N).ncard / (univ ∩ Iio N).ncard`; our definition uses
`(A ∩ Iio N).ncard / N`. These are equal because intersection with the universe
does not change a set and the number of natural numbers strictly below N is N.
Both definitions take the limit over all natural N, with values in the reals.
`source_statement_positive_density` formally proves the same result with the
reference's unsimplified density expression.

Our witness includes 1 and 2, so nonconstancy is not vacuous. It excludes 0.
The proof applies to every nonempty finite subset, without a size bound or a
computer search cutoff. The limit theorem proves density 1/2 exactly; the
existence quantifier is not weakened to positive upper or lower density.

Outside scope: P₁ for all naturals, odd naturals, all infinite arithmetic
progressions, or squares excluding 1; and the general unique-even-element
variant for arbitrary infinite sets. No catalog-wide solved/formalized flag is
requested on the strength of this subproblem alone.
