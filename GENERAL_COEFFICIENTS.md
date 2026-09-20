# Original coefficient domain and the completion

## Source and scope

Schinzel, *On the number of terms of a power of a polynomial*, Acta Arithmetica 49 (1987), 55–70, states the historical minimum question for complex coefficients on p.55 and proves a broader characteristic-zero-field estimate. [Primary paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa49/aa4916.pdf). Hayman's Problem 4.4, reproduced on printed p.73 of [Hayman–Lingham's 2018 edition](https://arxiv.org/abs/1809.07200v2), asks for a uniform support threshold for all polynomials. The Coppersmith–Davenport 13-term/12-term seed appears on printed p.86 of [their 1991 paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa58/aa5816.pdf).

The [external Formal Conjectures file at `5657b3b9ae1c174fdbab9d9d600b018238ba573c`](https://github.com/google-deepmind/formal-conjectures/blob/5657b3b9ae1c174fdbab9d9d600b018238ba573c/FormalConjectures/ErdosProblems/485.lean) uses rational coefficients. It is a narrower reference, contains an unfilled target, and is neither imported nor treated as an organizer-approved replacement for the original coefficient domain.

## Precise definitions and coverage

For a characteristic-zero field K, `JSP000393General.minimumSquareTerms K k` is literally the natural infimum of `{m | ∃ P : K[X], P.support.card = k ∧ (P^2).support.card = m}`. `minimum_attained` proves the set nonempty and that its infimum is an actual minimum. The rational embedding in that proof constructs one admissible polynomial for each k; the set still quantifies over **all** K-polynomials.

| Original obligation or disclosed consequence | Declaration |
| --- | --- |
| Arbitrary complex coefficients, with no extra algebraic assumptions | `complex_original`, an instance of the characteristic-zero-field theorem |
| A bound uniform over all polynomial coefficients and degrees | `schinzel_support_bound`, `schinzel_term_bound`, `uniform_threshold` |
| Minimum ranges over actual squares and is attained for every natural k | `minimumSquareTerms`, `minimum_attained`, `minimum_le` |
| Minimum tends to infinity as k tends to infinity | `minimum_diverges` |
| Explicit support counts 13^k and 12^k for every k | `family_counts` |
| Actual minimum upper bound at support sizes 13^k | `minimum_family_upper_bound` |
| Arbitrarily large support sizes with arbitrarily small relative square support | `arbitrarily_large_small_ratio` |
| Combined interface | `jsp_000393` |

The result concerns squares, not all powers. It does not claim an optimal bound or a sharp upper bound for every support size. Positive-characteristic fields are not included.

## Why the lower bound is unconditional

The fixed upstream project already proves Hajós' support bound, primitive normalization, the trinomial case, Dirichlet deformation, squarefree factorization, and recursive specialization over arbitrary characteristic-zero fields. Its final Schinzel wrapper happened to specialize those results to the rationals. The new wrapper performs strong induction directly on the number of square terms and applies those already-proved general-field components. The small branch uses the established arithmetic bound; the recursive branch has strictly fewer square terms and preserves the required support comparison. No assumed Schinzel reduction or external mathematical oracle is introduced.

## Contributions and version distinction

The original construction `JSP000393.lean` and rational integration `JSP000393Complete.lean` are unchanged. The new contribution is the general-field induction interface, the actual all-coefficient-field minimum and attainment proof, and transport of the existing sparse family to that domain. The mathematical argument and the 22 underlying formal modules retain their original attribution. The new completion date and commit must not be backdated to the original construction or rational-only proof.

## Selected revision and historical first attempt

The first 2026-09-19 general-field candidate `ed82d0cb2d35fca55f32b00cb75bdd5271226eb8` failed its warnings-as-errors check because `minimum_le` retained an unused automatic `CharZero` section parameter. The selected `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8` adds `omit [CharZero K] in` for that lemma and updates its checksum; the mathematical proof is unchanged. The first candidate is historical evidence, not a selected passing version. Only the selected revision’s own completed full self-check can establish its verification verdict; the separately dated report records that result.
