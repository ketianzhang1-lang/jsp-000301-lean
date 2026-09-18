# Original statement and exact correspondence

JSP-000140 is Erdős 136: determine the asymptotic minimum palette size f(n,4,5)
for colourings of genuine edges of Kn where each four-vertex clique has at least
five colours. [Bennett, Cushman, Dudek and Prałat, Theorem 1](https://arxiv.org/html/2207.02920v1)
establish f(n,4,5) = (5/6)n + o(n). No numerical onset or all-n exact formula
for the minimum is asserted by that asymptotic statement.

| Original object | Formal representation |
| --- | --- |
| Symmetric pair-colouring used in our lower proof | `JSP000140.Coloring`, `Admissible` |
| Genuine unordered-edge colouring | `SimpleGraph.TopEdgeLabeling`, `Erdos136.Is45Coloring` |
| Pair/edge equivalence for n >= 2 | `JSP000140.pairColorable_iff` |
| Attained minimum in our model | `JSP000140.minPalette`, `minPalette_spec` |
| Exact equality of minima for n >= 2 | `JSP000140.minPalette_eq` |
| Strict finite lower bound | `minPalette_strict_lower`, `minPalette_integer_lower` |
| Ratio limit and asymptotic equivalence | `minPalette_tendsto`, `minPalette_asymptotic` |
| Eventual actual colourings for every positive epsilon | `eventually_near_optimal` |
| Combined complete result | `JSP000140.jsp_000140` |

The bridge enumerates the six genuine edges of K4 and shows their image is
exactly the six pair-colours in our original predicate. Symmetry makes the
conversion independent of edge orientation. The reverse conversion chooses
an arbitrary diagonal colour; an actual edge proves that the palette is
nonempty when n >= 2. Our total minimum is defined for all natural n, but its
comparison to the standard minimum is deliberately limited to n >= 2, because
a single vertex has no genuine edges whereas a total pair-colouring still
requires a diagonal value. This does not affect the full asymptotic limit.

The general upper proof includes the complete conflict-free matching and
construction dependency chain. It is not supplied as an unproved hypothesis.
Our original strict lower theorem is applied to every competing admissible
colouring and to the attained minimum; the upper result supplies actual
colourings for every sufficiently large size, rather than a sparse subsequence.
The proof has no extra mathematical assumptions replacing a missing step.
Maintainer or independent human review is still needed for semantic fidelity.
