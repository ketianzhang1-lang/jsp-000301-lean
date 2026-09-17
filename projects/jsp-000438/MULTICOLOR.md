# Finite-color supplement to JSP-000438

This supplement proves the known Erdős–Sós consequence

\[
R(T_1,\ldots,T_r)\le 2+\sum_{i=1}^r (|T_i|-2),
\]

for every finite nonempty color set and every family of finite trees with at
least two vertices each. Tree orders may differ. It extends the two-color
integration already submitted in organizer PR #408; it is not a new solution
claim or a claim of new mathematics or first-formalization priority.

## Exact statements

`Multicolor.lean` contains four new checked endpoints:

| Declaration | Meaning |
| --- | --- |
| `JSP000438.sum_edges_of_cover` | A finite graph cover of a complete graph has at least its total number of edges, counted with multiplicity. |
| `JSP000438.multicolor_trees_monochromatic` | At the stated bound, some covering graph contains its corresponding tree; overlapping color classes are permitted. |
| `JSP000438.multicolor_tree_embedding` | For an actual coloring of unordered vertex pairs, there are a color and an injective vertex map preserving all tree edges in that color. |
| `JSP000438.multicolorGraphRamsey_trees` | The associated multicolor Ramsey number satisfies the bound. |

The direct embedding theorem supplies a member of the set used to define the
Ramsey number. No conclusion relies on taking the infimum of an empty set.
Containment is ordinary subgraph containment, with distinct tree vertices sent
to distinct host vertices. It does not assert induced containment.
Diagonal unordered pairs can receive arbitrary colors; they are removed by
`SimpleGraph.fromEdgeSet` and never represent tree edges.

## Proof and provenance

Write `S = sum_i (|T_i|-2)` and `N = S+2`. If every color avoids its tree,
the credited `Erdos548.tree_free_edge_bound` gives `2 e(G_i) ≤ (|T_i|-2) N`.
Coverage gives `N(N-1) ≤ 2 sum_i e(G_i) ≤ S N`. But `N-1 = S+1` and `N>0`,
which is a contradiction. The Lean proof implements the covering inequality,
the finite sum argument, and the conversion to a literal edge coloring.

The substantial tree-free theorem remains the upstream work of
[tadamcz/erdos548, pinned at 82ffb751f3d37768927df9239ed08439bbe0dd09](https://github.com/tadamcz/erdos548/tree/82ffb751f3d37768927df9239ed08439bbe0dd09).
Its original source, license, attribution and existing port are retained.
The new finite-color integration was prepared for Ketian Zhang with OpenAI
Codex assistance. The mathematical implication itself is standard; no
authorship of the upstream argument or priority over other implementations is
claimed. Award eligibility is for the organizer to assess.

## Verification

Use the committed Lean 4.34.0 toolchain and dependency manifest. Run
`bash scripts/verify.sh` and `bash scripts/verify_nanoda.sh` after obtaining
the dependencies with `lake exe cache get`.

The scripts check the original five endpoints and all four new endpoints.
They require warning-free compilation, bundled kernel replay, axiom closures
limited to `propext`, `Classical.choice`, and `Quot.sound`, actual dependency
revision checks, and rejection of a false arithmetic statement. The independent
NaNoda script exports and checks all nine endpoint dependency closures.
Successful execution must be established by the associated logs; describing
the scripts is not itself evidence that they ran.
