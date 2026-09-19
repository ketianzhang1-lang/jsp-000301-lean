# Statement correspondence for JSP-000476

The [catalog problem](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000476)
asks for the maximum cardinality of a subset of the integer interval `{1,...,N}`
whose nonempty subset sums are never squares. Nguyen–Vu determine its growth
as `N^(1/3+o(1))`.

We use `Finset ℕ`, restricted by `A ⊆ Finset.Icc 1 N`, for the positive integer
interval. Our original definition is

`SquareSumFree A := ∀ S ⊆ A, S.Nonempty → ∀ x : ℕ, ∑ a ∈ S, a ≠ x ^ 2`.

All subsets are quantified over. The empty subset is excluded, and the empty
ambient set is permitted. Testing natural square roots suffices for integer
squares because a negative root and its absolute value have the same square.
No restriction to progressions, prime multiples, bounded cardinalities, or
squarefree elements occurs in the complete endpoint.

| Requirement | Formal theorem in `JSP000476Complete.lean` |
| --- | --- |
| Our original admissibility predicate equals the upstream predicate | `squareSumFree_iff_upstream` |
| The finite maxima agree for every `N`, including zero | `extremal_eq_upstream` |
| Every admissible cardinality is bounded by the maximum | `card_le_extremal` |
| An admissible maximizing set exists for every `N` | `exists_extremizer` |
| Finite ambient bound and zero case | `extremal_le_interval`, `extremal_zero` |
| Monotonicity in the interval size | `extremal_mono` |
| Lower bound `N^(1/3)/4` for every `N ≥ 64` | `extremal_lower_bound` |
| Absolute positive constants for the upper bound, uniformly over all admissible sets | `uniform_polylog_upper_bound` |
| `N^(1/3+o(1))`, with an explicit threshold quantifier for each positive epsilon | `complete_extremal` |
| Direct original-problem statement: a large admissible set exists, and all admissible sets satisfy the upper bound | `complete_problem` |
| Sets above the upper threshold contain a nonempty square-sum subset | `eventual_square_forcing` |

The direct endpoint has the following quantifier order:

For **every** real `ε > 0`, there **exists** a natural `N₀` such that for
**every** natural `N ≥ N₀`:

1. there **exists** `A ⊆ {1,...,N}` with `SquareSumFree A` and
   `N^(1/3−ε) ≤ |A|`;
2. for **every** `A ⊆ {1,...,N}`, `SquareSumFree A` implies
   `|A| ≤ N^(1/3+ε)`.

The threshold depends on epsilon, not on the chosen set. The asymptotic result
does not claim an exact leading constant or an exact formula for each finite
maximum. It is the full growth conclusion proved in the cited Nguyen–Vu result.

The unchanged earlier `JSP000476.lean` additionally retains the exact criterion
for every positive step `d = b²a`, with squarefree `a`, for the particular family
`{d,2d,...,md}`. The new upper bound supplies the previously missing arbitrary-set
direction. See `PROVENANCE.md` for the prior complete formalization that supplies
the difficult upper-bound proof and our separate bridge contribution.

The theorem statements and their truth must be assessed together with the
exact-version verification receipt. Source preparation alone is not successful
verification.
