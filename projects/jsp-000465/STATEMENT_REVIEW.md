# Statement correspondence

The official catalog describes reducing an extremal problem for a forbidden
family containing a bipartite graph to one forbidden member. Chapter 10 of the
cited primary paper formulates constant-factor eventual comparison and gives a
counterexample in which every forbidden graph is connected, bipartite, and
contains a cycle.

| Informal object | Formal object | Scope check |
| --- | --- | --- |
| A finite simple graph | `Erdos180.FiniteGraph` | A natural vertex count and a Mathlib `SimpleGraph (Fin order)` |
| Finite forbidden family | `Finset FiniteGraph` | Explicitly nonempty in the counterexample |
| Ordinary subgraph avoidance | `Erdos180.FamilyFree` | Uses Mathlib `SimpleGraph.Free` for each member |
| Family extremal number | `Erdos180.familyExtremal` | Maximum edge count over all labelled family-free graphs of order n |
| One forbidden graph | `SimpleGraph.extremalNumber` | Singleton equivalence is checked in a new theorem |
| Connected and bipartite | `Connected` and `IsBipartite` | Both predicates come from Mathlib |
| Contains a cycle | `not IsAcyclic` | Required of every forbidden member |
| All sufficiently large host orders | `Filter.Eventually` at `atTop` on naturals | Not a finite sample or a selected subsequence |
| Uniform failure for every member | `JSP000465.uniform_separation` | The eventual threshold works for all members simultaneously |

The supplied `connected_bipartite_counterexample` proves the strengthened
restriction directly. `not_bipartite_compactness` negates the less restricted
universal question. The former prevents the latter from being supported merely
by the much easier disconnected forest example.

The new simultaneous consequence follows from the existing bounds as follows.
The family is finite, so all member lower bounds c*n^(4/3) eventually hold
together, with the fixed upstream c > 0. For K > 0, apply the upstream little-o
family bound with epsilon = c/(2*K). Multiplication by K leaves at most half of
the common positive lower bound. This yields strict separation.

The proof makes no claim about the optimal exponent or minimal size of a
counterexample family. No global novelty or priority is claimed for the
simultaneous reformulation. Formal statement review and contribution eligibility
remain organizer decisions.
