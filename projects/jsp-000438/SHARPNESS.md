# Sharpness of the full tree Ramsey bound

For every natural k, let T be the star on 2k+2 vertices, with 2k+1 leaves.
The supplement proves

\[
R(T,T)=4k+2.
\]

Together with the complete upper bound already submitted in organizer PR #408,
this proves that the bound R(T,T) <= 2n-2 is attained at every even tree order.
It cannot be decreased by one uniformly over all trees. The result is a
classical sharpness construction; no new mathematics or priority is claimed.
This is a supplement to the same submission and not a new reward application.

## Explicit coloring

Put N=4k+1 and label the vertices by the genuine cyclic group ZMod N.
For distinct a and b, let d be the canonical integer representative of b-a.
Color the edge red precisely when d is in [1,k] or [3k+1,4k].
Otherwise color it blue; then d is in [k+1,3k].
Replacing d by N-d preserves each color, so this defines an undirected graph.

For fixed a, encode a red neighbor by d-1 in the first interval and
d-2k-1 in the second interval. This is an injection into Fin(2k).
A blue neighbor is encoded by d-k-1, again injectively into Fin(2k).
Thus every vertex has at most 2k neighbors of each color.
An injective copy of T would require 2k+1 neighbors at the image of its
center, which is impossible. Lean uses Mathlib's actual non-induced graph
copies and its degree monotonicity theorem for this argument.

This supplies a counterexample on 4k+1 vertices. The proof also handles
every smaller host order: pull the coloring back along an injection into
the displayed cyclic vertex set. Both colors embed in the original colors,
so neither can acquire a forbidden star. The defining Ramsey set is known
to be nonempty from the proved tree upper bound; its natural infimum is
therefore not being evaluated on an empty set.

The original upper bound gives R(T,T) <= 2(2k+2)-2 = 4k+2.
The lower and upper bounds yield equality. When k=0 the counterexample has
one vertex and no edges, and T has two vertices; the same proof applies.

## Formal statements

- `sharpGraph`: the explicit graph on ZMod(4k+1).
- `sharpGraph_degree_le` and `sharpGraph_compl_degree_le`: both degree bounds.
- `sharpGraph_avoids_star`: absence of the target star in both actual colors.
- `card_lt_graphRamsey_of_counterexample`: reusable lower-bound transfer,
  with the necessary Ramsey-set nonemptiness premise explicit.
- `star_ramsey_even_order`: the exact Ramsey number for every even-order star.
- `tree_ramsey_bound_is_sharp`: the full universal upper bound and matching
  examples at every even order, in a single statement.

## Attribution and verification

The new formal code in StarSharpness.lean was prepared with OpenAI ChatGPT
assistance. It uses Mathlib's star graphs, finite graph copies, cyclic groups,
and cardinality infrastructure. The proof of the general tree upper bound
continues to use the fully credited tadamcz/erdos548 dependency; all original
notices and the exact port patch are retained. No authorship of that upstream
mathematics or formal proof is reassigned.

The local supplement compiled under Lean 4.34.0 with warnings as errors;
the five new endpoint axiom closures contain only propext, Classical.choice,
and Quot.sound. The updated verification scripts check ten total endpoints,
replay all four proof modules, verify locked dependency revisions, and require
rejection of a false arithmetic control. A remote receipt must record an
actual successful run before remote verification is claimed.

The supplement belongs with the original PR #408. Review and prize decisions
remain with the organizers; these contributor-run checks are not a referee
attestation or payment authorization.
