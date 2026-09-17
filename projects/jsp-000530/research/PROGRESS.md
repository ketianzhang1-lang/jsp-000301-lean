# JSP-000530: verified research progress, with the remaining problem explicit

We have not completed JSP-000530. We provide fifteen proved Lean lemmas that
clarify the remaining lower-bound target and rule out a natural attempted repair
of the two-axis counterexample. These are research additions, not a complete
prize submission. We make no claim of a new solution or first formalization.

## Corrected scope

The remaining problem is broader than merely removing three collinear points
from the existing construction. In [Erdős's 1987 paper, printed page
168](https://www.renyi.hu/~p_erdos/1987-27.pdf#page=2), the questions include a
uniform improvement above the one-third pinned-distance bound, and a
general-position construction with a fixed fractional loss from n distances.
Erdős also asks whether the lower-bound improvement survives the weaker
no-four-concyclic hypothesis. His coefficient `(1+c)/3` can equivalently be
written `1/3+c'` with another positive constant.

Our existing two-axis proof disproves the near-n assertion under only the
no-four-concyclic condition. It does not settle the positive lower-bound
improvement, with or without the additional no-three-collinear condition.
[Feng et al., Section 3.1, Remark 3.1](https://arxiv.org/html/2601.22401v3#S3.SS1)
also explain the limit of the two-axis result. The [public problem
registry](https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml)
continues to list problem 654 as open at the time of this review. No complete
solution of the remaining questions was located in this investigation.

The earlier README's focus on collinearity alone was an incomplete account of
the scope gap. Even a successful general-position modification of the existing
counterexample would not by itself prove the positive lower-bound improvement.

## Exact reduction of the lower-bound target

For p in an n-point set S, let d(p) be the number of distinct distances from p
to S excluding p. Group the other points according to their distance from p.
The no-four-concyclic assumption bounds each group size by three. Define

```text
W(p) = sum over distance groups of (3 - group size).
```

We prove the exact identities

```text
n - 1 + W(p) = 3 d(p),
W(p) = 2 s1(p) + s2(p),
```

where s1 and s2 count groups containing exactly one and two points,
respectively. Consequently, for any real c,

```text
d(p) > (1/3+c)n    if and only if    W(p) > 3cn+1.
```

The main equivalence `uniform_improvement_iff_slack` includes the full
quantifiers: a constant independent of S and n, all sufficiently large n,
every admissible finite point set, and a base point belonging to that set.
The known baseline follows by W(p) >= 0. A bounded additive improvement is
insufficient: completing the lower-bound question requires W(p) to exceed a
positive constant times n, uniformly. We have not proved that geometric step.

The unresolved assertions `UniformDistanceImprovement`,
`GeneralPositionImprovement` and `UniformSlackImprovement` are ordinary
proposition definitions. They are not axioms or theorems asserted as facts.

## Why preserving the old reflected pairs cannot work

For two distinct points u and v, every point equidistant from them lies on
their perpendicular bisector. We prove directly in real coordinates that
three such centers are collinear, and derive an at-most-two-centers theorem
under `NoThreeCollinear`.

The old two-axis proof relies on many centers on one axis seeing opposite
points on the other axis at equal distances. Any deformation preserving that
same pair equality at three distinct centers must keep those centers collinear.
A repair therefore needs a different pattern of repeated distances; simply
keeping the old equalities while moving the centers into general position
cannot succeed. This rules out that mechanism, not all possible constructions.

## Quadratic bending fails in two independent ways

Consider the explicit deformation

```text
(x,0) -> (x,t x^2),       (0,y) -> (t y^2,y).
```

First, the squared-distance difference from the bent x-point to the two bent
y-points with parameters y and -y is exactly `-4 t x^2 y`. For nonzero t, x,
and y, the crucial equality is lost. This is an exact real-algebra identity,
not a numerical tolerance observation.

Second, for any nonzero t, the four bent x-points with parameters 2, -2, 4,
and -4 lie on one circle. More generally, the two opposite pairs with
parameters ±a and ±b share a circle with center

```text
(0, (1 + t^2(a^2+b^2))/(2t)).
```

`quadratic_bending_not_no_four` proves the four-point failure for every
nonzero real t using the same `NoFourConcyclic` predicate as the original
formalization.

## Exact finite diagnostics

The accompanying Python program uses integer determinants and squared
distances, with no floating-point comparisons. At t = 1/10000 it gives:

| Number of points | Original maximum distance count | Bent maximum distance count | Bent collinear triples | Bent concyclic quadruples |
| --- | --- | --- | --- | --- |
| 8 | 5 | 7 | 0 | 2 |
| 12 | 8 | 11 | 0 | 6 |
| 16 | 11 | 15 | 0 | 16 |
| 24 | 17 | 23 | 0 | 64 |
| 32 | 23 | 31 | 0 | 166 |

These samples corroborate the failure of this candidate. They do not establish
an asymptotic bound or replace the real-variable Lean theorems.

## Source, verification and contribution

- Branch: `jsp-000530-general-position-research`.
- Proof file: [JSP000530Research.lean](../JSP000530Research.lean).
- Exact-type and axiom checks: [AuditResearch.lean](../AuditResearch.lean).
- Reproduction: [verify_research.py](../scripts/verify_research.py).
- Exact finite program: [perturbation_check.py](perturbation_check.py).
- [Machine-readable local verification](verification/verification.json).

We identify GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT assistance,
as the contributor of these Lean implementations, reductions, candidate checks
and research documentation. The one-third baseline and perpendicular-bisector
geometry are classical facts. The prior two-axis mathematical attribution is
unchanged. We do not present these research lemmas as a complete solution.

All fifteen new theorem closures and the six existing audited targets passed
the axiom checks, using only `propext`, `Classical.choice` and `Quot.sound`.
Both modules compiled with warnings treated as errors and passed Lean's bundled
kernel replay. All nine dependency revisions matched the pinned manifest, and
the false-arithmetic negative control was rejected. The raw local record
preserves the repository HEAD used while preparing the new commit; its source
hashes identify the actual checked files. Compilation and replay use cached
Mathlib dependencies and are contributor-run checks.

From `projects/jsp-000530`, with the pinned Lean 4.34 toolchain:

```bash
lake exe cache get Mathlib.Analysis.Complex.Basic Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Push
python3 scripts/verify_research.py
python3 research/perturbation_check.py
```

The next substantive requirement is a new geometric bound forcing linear
singleton/doubleton slack, or a genuinely different construction resolving the
relevant remaining question. Neither has been established here. PR #348 remains
incomplete; these research files are not added to the prize repository.
