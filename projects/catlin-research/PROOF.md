# Proof and statement fidelity

## The explicit graph

The vertices are Fin 15, partitioned into five clusters of size three by
`cluster(v) = floor(v/3)`. Distinct vertices are adjacent precisely when
their clusters are equal or consecutive modulo five. This is C5[K3].

## Chromatic number

Every independent set has at most two vertices. The inherited finite theorem
`no_independent_triple` checks every triple. For any hypothetical proper
7-colouring, `colour_fiber_card_le_two` applies that theorem to each colour
class. Summing the seven fibre cardinalities gives 15 <= 14, a contradiction.

The eight colour classes

{0,6}, {1,7}, {2,9}, {3,10}, {4,11}, {5,12}, {8,13}, {14}

are verified to be proper. `chromaticNumber_eq_eight` therefore states exact
equality with 8 using Mathlib's `SimpleGraph.chromaticNumber`, not a separate
numerical surrogate.

## Faithful subdivision model

For a branch set B, `edgeSet B` contains every pair (u,v) in B x B with u < v.
Thus every unordered pair of distinct branch vertices occurs exactly once.
`Subdivision B` supplies a Mathlib `graph.Walk u v` for each of these pairs,
requires each walk to be a simple path, requires its internal vertices to
avoid B, and requires interiors of distinct paths to be disjoint.
`ContainsCliqueSubdivision r` asserts existence of such a B of cardinality r.

This is a direct path definition of a complete-graph subdivision. In
particular, neither the finite arithmetic obstruction nor the absence of a
subdivision is assumed in the model.

## Lower bound on required internal vertices

For u < v in B, assign demand zero to an adjacent pair. For a nonadjacent
pair, assign demand one if some vertex outside B is adjacent to both u and v,
and demand two otherwise. Assign zero to other ordered pairs.

`GraphCore.lean` proves, by decomposing genuine walks, that a path between
nonadjacent distinct endpoints has length at least two. If there is no
available common neighbour, its length is at least three. A simple path of
length L has exactly L-1 internal vertices. Hence each demand is no larger
than the corresponding interior cardinality.

Let c_i be the number of branch vertices in cluster i. Each c_i is at most
three, and their sum is the cardinality of B. For nonadjacent clusters i,j,
every common neighbour is in the middle cluster m = 3(i+j) mod 5. If c_m=3,
that whole middle cluster is occupied by branch vertices, so each such pair
has demand at least two. Otherwise using a lower bound of one is sufficient.

Define the cluster weight w(i,j) to be zero except for i<j in nonadjacent
clusters, where it is two if c_m=3 and one otherwise. The finite theorem
`profile_certificate` checks all 4^5 cluster-count functions and proves

    sum_i c_i = 8  ==>  sum_i sum_j c_i*c_j*w(i,j) >= 8.

This uses `decide +kernel`, not native evaluation or an external solver.
`regroup_twice`, `full_cluster`, and `weight_le_demand` connect that finite
certificate to an arbitrary branch set and prove `budget_ge_eight`.
The proof does not assume branch vertices occupy initial segments of clusters.

## Upper bound from disjointness and the contradiction

The union of the path interiors is disjoint from B. Pairwise disjointness
makes its cardinality equal to the sum of the interior cardinalities.
Since the union together with B is a subset of Fin 15,

    budget(B) + |B| <= 15.

For |B|=8, the lower bound gives budget(B)>=8, whereas this upper bound gives
budget(B)<=7. The contradiction is `no_K8_subdivision`. Combining it with
the chromatic-number theorem gives `catlin_counterexample`.

The earlier `Certificate.lean` also contains a stronger finite resource
formula with lower bound 12. The present completed path bridge uses the
simpler demand bound above; it does not claim to have formalized the older
12-bound's capacity-allocation argument.

## Attribution and prize boundary

Catlin disproved Hajos's conjecture in 1979. The mathematical background and
distinction from the asymptotic Erdos-Fajtlowicz problem are described in:

- Fox, Lee and Sudakov, *Chromatic number, clique subdivisions, and the conjectures of Hajos and Erdos-Fajtlowicz*, https://arxiv.org/abs/1107.1920.
- JSP-000585 catalog, https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#jsp-000585.

JSP-000585 concerns a uniform bound of order sqrt(n)/log(n) for the ratio
of chromatic number to largest clique-subdivision order. This single finite
counterexample does not establish that statement. A public formalization
source for that different asymptotic theorem is already present at
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos717.lean.
It was not imported into this proof or independently rebuilt here.

The current contribution is the formal graph-path and colouring completion
of the submitting account's earlier finite checkpoint. No mathematical
novelty, global first-formalization priority, organizer approval, award,
or payment entitlement is asserted.
