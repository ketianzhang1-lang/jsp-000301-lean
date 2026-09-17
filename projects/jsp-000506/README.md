# JSP-000506: Heckel's concentration reduction

**Development status: not yet verified or submitted for prize review.**

This project formalizes Proposition 3 of Annika Heckel's *On a question of
Erdős and Gimbel on the cochromatic number*, Electronic Journal of Combinatorics
31(4) (2024), P4.72, DOI https://doi.org/10.37236/13346.
Author preprint: https://arxiv.org/abs/2408.13839.

For every graph order `n` and natural number `g`, if a uniform random simple
labelled graph has `chi - zeta <= g` with probability at least 999/1000, there
is an integer `k` for which `k <= chi <= k+g` has probability greater than 9/10.
Here `chi` is the chromatic number and `zeta` is the cochromatic number.

The main target is `JSP000506.heckel_proposition3`. It has exactly the
gap-probability premise in the mathematical proposition. Auxiliary monotonicity,
complement symmetry, and `zeta <= chi` are proved, not assumed in that target.
The more general `concentration_reduction` applies to any increasing natural
statistic on a finite Boolean cube and a complement-invariant smaller statistic.

## Exact representation

`Edge n` consists of pairs `(i,j)` in `Fin n` with `i<j`. Every unordered pair
is represented once. A `Finset (Edge n)` is a simple labelled graph. Uniform
counting over its power set is exactly the `G(n,1/2)` distribution: all
`2^(card (Edge n))` possible graphs receive the same weight. Probabilities
are exact rational numbers, with no simulation or floating-point arithmetic.

`Proper` is a vertex coloring with no equal-colored adjacent pair. `CoProper`
assigns a vertex color and a Boolean to each color class, indicating a clique
or an independent set. The chromatic and cochromatic numbers are the minimum
numbers of colors, whose existence is proved using the identity coloring.
The zero-vertex case is included.

## Scope and credit

This is a formalization of known mathematics, attributed to Heckel. It is a
component of JSP-000506 / Erdős 625; it does **not** prove the full random-graph
asymptotic result, a diverging lower bound for `chi-zeta`, or the later result
credited to Petkov and GPT-5.6. It does not claim a new mathematical discovery,
global first-formalization priority, or award eligibility. Mathlib's existing
Harris-Kleitman theorem supplies the correlation inequality and remains credited
to its authors, including Yaël Dillies. This implementation was independently
written with OpenAI ChatGPT assistance for the submitting account.

The catalog and available issue/PR records were checked on September 17, 2026;
no JSP-000506 filing was found in that scoped check. This is not a guarantee
that no relevant proof exists elsewhere. A later global search located the
existing SamPetkov/Erdos formalization of a stronger asymptotic result; see
`PRIOR_ART.md`. No first-Lean claim is made. Any recipient identity remains
`RECIPIENT-JSP-000506-KZ-A`, confirmation pending.

## Reproduction

Lean 4.34.0 and the complete Mathlib dependency graph are pinned by
`lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake build --wfail
lake env leanchecker --fresh JSP000506
lake env lean Audit.lean
```

No successful build is claimed until the actual run is recorded. Repository
record checks, proof compilation, and organizer acceptance are separate steps.
New code is licensed under Apache-2.0; no article text or PDF is redistributed.
