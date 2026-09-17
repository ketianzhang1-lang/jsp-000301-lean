# JSP-000140 / Erdos 136: strict lower bound for (4,5)-colorings

**Scope: the classical lower-bound component, with strictness and exact integer
rounding. This is not the full asymptotic solution of JSP-000140.**

For every n >= 4 and every symmetric edge coloring of K_n using a palette of
k colors, if each four-element vertex subset sees at least five colors, then

    5*(n-1) < 6*k,
    floor(5*(n-1)/6) + 1 <= k.

All n and k are universally quantified. No finite testing range is substituted
for this claim. Colors assigned on the diagonal are ignored, and symmetry is
an explicit hypothesis. The lower-bound constant 5/6 is classical.

## Proof structure

An ordered fork is a triple (v,a,b) of distinct vertices with equal colors on
va and vb. The four-vertex condition excludes a monochromatic triangle and
forces the three directed edges (v,a), (a,b), (b,v), for all ordered forks,
to be distinct. If F counts ordered forks, this gives 3F <= n(n-1).

For vertex v and color c let d(v,c) count its neighbors in color c. Exact fiber
counting gives sum d = n(n-1) and sum d(d-1) = F. The elementary inequality
2d <= 2+d(d-1) gives 2n(n-1) <= 2nk+F. Combining the bounds yields
5(n-1) <= 6k.

If a fork exists, its closing-edge color does not appear at its center, so one
degree is zero and the incidence inequality is strict. If no fork exists,
the coloring is proper at every vertex, which also gives the strict 5/6 bound
for n >= 4. The Lean proof includes both cases.

## Main endpoints

- `JSP000140.edgeImage_injective`: all three directed edges of ordered forks
  are distinct, across every pair of forks.
- `JSP000140.fork_packing`: 3F <= n(n-1).
- `JSP000140.fork_card_eq`: exact correspondence with color-degree fibers.
- `JSP000140.strict_lower_bound`: 5*(n-1) < 6*k.
- `JSP000140.integer_lower_bound`: the rounded integer bound.
- `JSP000140.lower_bound_from_vertex_sets`: the same bound under the standard
  hypothesis that each four-element subset sees at least five colors.

`edgeColors` uses the image of the off-diagonal ordered pairs. Symmetry makes
this exactly the color set of the usual six unordered edges. `edgeColors_four`
proves that correspondence explicitly.

## Sources and attribution

- [Prize catalog JSP-000140](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000140).
- [Erdos Problem 136](https://www.erdosproblems.com/136).
- Bennett, Cushman, Dudek and Pralat, [The Erdos-Gyarfas function f(n,4,5) =
  5n/6 + o(n)](https://arxiv.org/html/2207.02920v1), Theorem 2 and its discussion.
  That source attributes the lower-bound proof to Erdos and Gyarfas, with an
  earlier statement by Erdos, Elekes and Furedi. Its asymptotic upper-bound
  construction is outside this package.

Existing public Lean work must be disclosed: the pinned
[plby/lean-proofs entry](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean)
already declares the full asymptotic result, and its `Erdos136/LowerBound.lean`
provides an existing lower-bound formalization. Those declarations were inspected
for scope; their dependency closure was not rebuilt or independently audited in
this project. This package imports none of that repository and contains no
copied third-party proof code. It is an independently written finite counting
proof against Mathlib, prepared with OpenAI ChatGPT assistance for the submitting
account `ketianzhang1-lang`. Mathematical novelty, first-formalization priority,
and an improved best-known bound are not claimed.

A limited search of official issues and PRs for JSP-000140 on 2026-09-17 returned
no match at preparation time. This does not establish priority or eligibility.
The catalog says Eligible to claim: No. Any recognition of this separate
implementation is for the organizers to assess. No award is announced.

## Reproduction

Lean v4.34.0 and Mathlib v4.34.0 (revision
5ed2965256430c3649e86755f9576b54eca72435), with all transitive revisions locked.

```sh
lake exe cache get Mathlib.Data.Finset.Card Mathlib.Data.Fintype.Card Mathlib.Data.Finset.Prod Mathlib.Data.Finset.Sigma Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The harness is adapted from the submitting account's JSP-000881 package. It
requires a build with warnings treated as errors, two Lean kernel replays, ten
axiom audits, locked dependency checks, rejection of an invalid arithmetic
proof, and a separate NaNoda check of four endpoints and their dependency closure.
See VERIFICATION.md for checks actually completed and their limits.

The [dedicated cloud run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178843250) passed every stage, including the separate NaNoda check of 6,554 declarations.
