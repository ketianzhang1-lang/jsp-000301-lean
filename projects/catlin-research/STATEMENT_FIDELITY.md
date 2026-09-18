# Original statement and formal correspondence

JSP-000585 corresponds to Erdős 717. Fox, Lee and Sudakov's
[Theorem 1.1](https://arxiv.org/pdf/1107.1920), page 2, resolves the
Erdős–Fajtlowicz upper-bound question: an absolute positive constant bounds
chi(G)/sigma(G) by C sqrt(n)/log(n) for every n-vertex graph with n >= 2.
The older random-graph lower estimate explains the order of the conjecture;
this package does not claim a formal random-graph asymptotic lower proof.

| Mathematical object | Lean representation |
| --- | --- |
| Arbitrary finite simple graph | `SimpleGraph V`, `[Fintype V]` |
| Chromatic number | `Erdos717.chiNat G = G.chromaticNumber.toNat` |
| Complete subdivision | Actual simple walks between injective branch vertices, with pairwise disjoint interiors avoiding every branch vertex |
| Largest subdivision order | `Erdos717.cliqueSubdivisionNumber G`, attained and bounded by the vertex count |
| Ratio chi/sigma | `JSP000585.ratio G`; sigma is proved positive for n >= 2 |
| Uniform original upper bound | `JSP000585.exists_universal_ratio_bound` |
| Extremal function | `JSP000585.extremalRatio n`, supremum over all graphs on `Fin n` |
| Extremal upper bound | `JSP000585.extremal_upper_bound` |
| Full package endpoint | `JSP000585.jsp_000585` |

The indexed model requires every branch pair, simple paths, disjoint interiors,
and branch avoidance. JSP000585Bridge proves exact equivalence with our earlier
finite-set model. A sorted enumeration gives one direction; recovering the branch
set and reversing paths when vertex order differs gives the other. The proof
includes r = 0. JSP000585Complete then identifies this model with Erdos717's.
The general conclusion is quantified over all finite simple graphs and assumes
only n >= 2, with no restriction on density, connectedness or independence number.

The full upper proof is the pinned Erdos717 development and its complete transitive
closure. Its absolute constant need not be optimal. We do not claim the particular
numerical constant printed in the paper. Our new constant lower bound is a
necessary condition obtained by evaluating any uniform bound at our exact
15-vertex example; it is not a matching asymptotic lower estimate.

No conjectured graph theorem is introduced as a proof premise. The audit and
NaNoda checks cover the full imported theorem dependency closure together with
all public theorems of our original and new modules. Semantic correspondence
still requires maintainer or independent human review.
