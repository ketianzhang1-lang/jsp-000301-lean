# JSP-000843: Mycielski's all-parameter upper-bound construction

This is a proposed **formalization of a known component**, not a solution of the
open sharp-asymptotic or consecutive-minima-ratio questions.

For every integer k >= 2, the Lean theorem `JSP000843.exists_for_every_k` constructs
a finite simple graph with exactly `3 * 2^(k-2) - 1` vertices, no triangle, and
chromatic number exactly k. In the catalog's notation this gives the classical
upper bound `h_3(k) <= 3 * 2^(k-2) - 1`.

## Mathematical argument

Start with K2. Given a graph G, retain its vertices, add a shadow for each vertex,
and add one apex. For each old edge vw, retain vw and add the two cross edges
v--shadow(w) and shadow(v)--w. Connect the apex to every shadow and to no original.
There are no shadow--shadow edges.

A triangle containing the apex is impossible. Any remaining triangle projects
to a triangle in G, so triangle-freeness is preserved. A coloring of G extends
by giving each shadow its original's color and giving the apex a new color.

Conversely, suppose the new graph has an (n+1)-coloring. Whenever an original
has the apex's color, recolor it with its own shadow's color. Adjacent originals
cannot both have had the apex's color; the cross edges prove that the recoloring
is proper. Shadow colors avoid the apex's color, so the resulting coloring of G
uses at most n colors. This proves the required lower bound on chromatic number.

After r iterations, chromatic number is r+2 and order satisfies
N_0=2, N_(r+1)=2*N_r+1. Thus N_r=3*2^r-1.

## Statement fidelity

The final theorem uses Mathlib's `SimpleGraph`, `CliqueFree 3`, `chromaticNumber`
and `Fintype.card`. It does not assume triangle-freeness or the chromatic bound
as unproved hypotheses. A temporary triangle predicate is proved equivalent to
Mathlib's clique predicate. The construction works for every natural iteration
count, not a finite list of tested graph sizes. Edges are undirected and loopless
by the SimpleGraph structure; exact colorability and non-colorability are proved.

The final theorem does not assert that these graphs have minimum possible order.
For example, it proves existence at k=4 with 11 vertices, but does not prove that
10 vertices are impossible. It makes no asymptotic sharpness claim.

## Attribution

The mathematical construction and result are due to Jan Mycielski, *Sur le
coloriage des graphes*, Colloquium Mathematicum 3(2) (1955), 161-162,
DOI [10.4064/cm-3-2-161-162](https://doi.org/10.4064/cm-3-2-161-162).
[Original article scan](https://matwbn.icm.edu.pl/ksiazki/cm/cm3/cm3119.pdf).
The article scan could not be retrieved by the preparation environment; the
bibliographic citation and the classical construction are separately identified.
The [NetworkX reference](https://networkx.org/documentation/stable/reference/generated/networkx.generators.mycielski.mycielski_graph.html)
provides an independently maintained implementation description.

The formalization was written for this submission with OpenAI ChatGPT assistance
under the submitting account's direction. It relies on the credited Mathlib and
Lean libraries. No mathematical discovery, independent human review, or global
first-formalization priority is claimed.

## Reproduction

Lean 4.34.0 and all dependency commits are pinned in lean-toolchain and
lake-manifest.json. From this directory:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as errors, replays the module with
Lean's bundled leanchecker, audits eight target declarations against the standard
axiom allowlist, checks actual dependency commits, and tests that false arithmetic
is rejected. The second script exports target dependency closures to an independent
NaNoda checker using a strict three-axiom allowlist.

Verification results and the exact tested commit are reported separately only
after the actual workflow completes. Cached Mathlib and network access are used.
