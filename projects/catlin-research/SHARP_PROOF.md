# Exact subdivision order of the Catlin graph

This supplement proves, for the explicit graph C5[K3], that its chromatic
number is 8 and it contains a subdivision of K_r exactly when r <= 7.
It extends the account's earlier proof of chromatic number 8 and absence of
a K8 subdivision. The known mathematical counterexample is credited to Catlin;
no novelty or first-formalization priority is claimed.

## Constructing K7

Use branch vertices B = {0,1,2,3,4,5,6}. All branch pairs are already adjacent
except {0,6}, {1,6}, and {2,6}. Replace those three pairs by the paths

| Pair | Path | Internal vertices |
| --- | --- | --- |
| {0,6} | 0,12,9,6 | {12,9} |
| {1,6} | 1,13,10,6 | {13,10} |
| {2,6} | 2,14,11,6 | {14,11} |

Each consecutive pair is an edge of C5[K3]. The six internal vertices are
distinct and outside B. The remaining 18 branch pairs use their direct edge.
Thus all 21 paths are simple, have pairwise disjoint interiors, and avoid all
branch vertices internally. Lean verifies these properties for actual Mathlib
walks in `sevenSubdivision`, using ordinary kernel reduction.

## Proving the exact threshold

`Subdivision.restrict` keeps the old paths between vertices of a smaller
branch set. Simplicity and disjointness persist, including avoidance of the
smaller branch set. This gives `containsCliqueSubdivision_antitone`.

Every r <= 7 is therefore attained by restricting the displayed K7. If r >= 8
were attained, restriction would produce a K8 subdivision, contradicting the
previously proved `no_K8_subdivision`. The endpoint is
`CatlinComplete.sharp_catlin_counterexample`.

The empty case r=0 is included: the empty branch set and empty collection of
paths satisfy the same definition without an exceptional convention.

## Scope and contribution

The new code is `Sharp.lean`: an explicit lower-bound witness, a reusable
restriction map for the existing subdivision model, and the exact classification.
It was written with OpenAI ChatGPT assistance. The original proof modules and
their attribution are retained. The build configuration now registers all local
modules, fixing the earlier clean-build failure `unknown module prefix Profile`.

This is a finite result related to JSP-000585 / Erdos 717. It does not prove
the catalog's uniform asymptotic bound for arbitrary finite graphs. Any
recognition of this scoped formalization remains for the organizers to decide.
Verification or submission does not establish award entitlement.
