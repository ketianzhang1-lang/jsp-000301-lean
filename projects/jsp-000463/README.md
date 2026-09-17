# JSP-000463: finite-field incidence lower bound

This package formalizes the **known biaffine-plane lower construction** for
JSP-000463 / Erdős Problem 573. It is partial scope relative to the original
conjecture `ex(n; {C3,C4}) ~ (n/2)^(3/2)`.

For every finite field K of cardinality q, the package constructs a simple graph
on exactly 2q² vertices with exactly q³ edges and no triangle or 4-cycle. It also
proves `q³ ≤ exC3C4(2q²)`. Instantiating with ZMod p proves this for every prime p,
and Euclid's theorem gives arbitrarily large orders. The final graph theorem
proves the exact identity `8 e² = n³` on an unbounded sequence of such graphs.

This is a uniform mathematical construction, not a finite list of examples.
It does not prove a matching upper bound, a limit, or an all-order asymptotic.
The universal finite-field theorem takes a field as input; this package does
not separately construct a field for every prime-power cardinality.

## Proof and original-statement correspondence

The vertices are a disjoint union of two copies of K×K. The first contains
points (x,y), and the second contains nonvertical lines (a,b). Adjacency is
defined by y=ax+b, and only joins different sides.

1. A bipartite graph cannot contain a triangle; the proof checks this directly.
2. Four incidences between two points and two lines imply
   `(a-c)(x-u)=0`. The field has no zero divisors, so either the points or the
   lines coincide. Hence no injective 4-cycle exists.
3. The lines through a point are parametrized by their slopes a, with unique
   intercept y-ax. The points on a line are parametrized by x. Every degree is q.
4. The degree-sum formula gives `2e=(2q²)q`, hence e=q³.
5. A graph isomorphism transports the construction to `Fin (2q²)`.
6. `exC3C4` is the finite supremum of actual edge counts among all graphs on
   `Fin n` avoiding both cycles; the constructed graph belongs to that family.

The forbidden configurations are Mathlib's `cycleGraph 3` and `cycleGraph 4`
with `SimpleGraph.Free`. They exclude ordinary subgraph copies, not just
induced cycles. `finite_field_construction` and `unbounded_graphs` include both
conditions in their conclusions. The definition of `exC3C4` imposes both.

## Attribution and prior work

The mathematics is classical finite geometry and is not claimed as a discovery.
For historical context and the original extremal problem, see Zoltán Füredi and
Miklós Simonovits, *The history of degenerate (bipartite) extremal graph problems*,
[arXiv:1306.5167v2](https://arxiv.org/html/1306.5167v2), §§3.1 and 4.8.
Section 3.1 describes affine/projective incidence constructions and credits
Kővári, T. Sós, Turán, and Reiman. The present graph is the affine incidence
construction with the vertical-line parallel class omitted. Section 4.8 states
the Erdős–Simonovits conjecture for the pair C3,C4.

[Official PR #313](https://github.com/TheJustinSunPrize/awards/pull/313) and
[Issue #314](https://github.com/TheJustinSunPrize/awards/issues/314), by
`baobingzhang` with Claude assistance, already provide an upper-bound
formalization and explicitly leave the lower construction unformalized.
The inspected PR head was `e47d4733cfb1a3de9844698922d0c5157c96f2cb`; its linked
proof revision was `6bec8a3c049d4295ce1cd60126d4093033b674db`.
That upper-bound code is not imported here. Its authors retain full credit.
The finite-supremum definition follows the same standard pattern used in
Mathlib and PR #313. No global first-formalization priority is asserted.

This package was developed for the submitting account `ketianzhang1-lang`
with OpenAI ChatGPT assistance. Proposed public recipient placeholder:
`RECIPIENT-JSP-000463-KZ-A`, confirmation pending. This is a self-submission for
review of the lower-construction formalization, distinct in scope from #313.
Whether this constitutes eligible partial formalization progress is for the
organizers to decide under their published rules. No award or payment is claimed.

## Reproduction

Lean: `leanprover/lean4:v4.34.0`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (tag v4.34.0).
All nine dependency revisions are locked by `lake-manifest.json`.

```bash
lake exe cache get Mathlib.Combinatorics.SimpleGraph.DegreeSum Mathlib.Combinatorics.SimpleGraph.CycleGraph Mathlib.Combinatorics.SimpleGraph.Extremal.Basic Mathlib.Data.ZMod.Basic Mathlib.Data.Nat.Prime.Infinite Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The scripts compile with warnings treated as errors, replay the module through
Lean's bundled checker, audit eleven declarations, check dependency pins, reject
a false arithmetic statement, and independently inspect small prime instances.
A composite-modulus negative control confirms that the field hypothesis matters.
NaNoda independently checks the exported target dependency closures and rejects
every axiom except propext, Classical.choice, and Quot.sound.

These are contributor-run verification steps, not organizer certification or an
independent human review. Mathlib binary caches and network access are used.
See VERIFICATION.md for actual execution results and limitations.
