# Catlin's graph: exact finite certificates and a complete human-readable argument

## Scope and status

This package concerns the known counterexample C5[K3] to the original Hajos
conjecture. It is **not a solution or complete Lean formalization of
JSP-000585 / Erdos Problem 717**. That problem asks for a uniform asymptotic
upper bound relating chromatic number and clique-subdivision number over all
finite graphs. A single Catlin graph does not prove that theorem.

The counterexample is attributed to Catlin in the literature. This package
makes no discovery, priority, prize eligibility, official verification, award,
or payment claim. It is research material, not a prize submission.

`Certificate.lean` contains finite arithmetic and graph-fact certificates.
It does **not** contain the graph-theoretic path-counting bridge below, a
formal chromatic-number theorem, or the asymptotic theorem of Fox, Lee and
Sudakov. Lean compilation, if successful, verifies only its actual theorem
statements. See the separate CI transcript for the compilation result.

## Graph

Let the vertex set be {0,...,14}. Partition it into five clusters
V_i={3i,3i+1,3i+2}, indexed modulo 5. Join distinct vertices when their clusters
are equal or consecutive on the five-cycle.

There are 15 within-cluster edges and 45 between-cluster edges, hence 60 edges.

## Chromatic number: exactly 8

An independent set contains at most one vertex per cluster, since each cluster
is a clique. Its occupied clusters form an independent set in C5. Three
clusters cannot be mutually nonconsecutive on a five-cycle: separating three
chosen clusters would require at least three unchosen clusters, whereas only
two remain. Thus every independent set has size at most two.

Every proper colour class therefore has at most two vertices. Covering the 15
vertices requires at least ceiling(15/2)=8 colours.

An explicit proper 8-colouring has the following colour classes:

{0,6}, {1,7}, {2,9}, {3,10}, {4,11}, {5,12}, {8,13}, {14}.

Every pair listed lies in nonconsecutive clusters, so these are independent
sets. Therefore the chromatic number is exactly 8.

The Lean file separately checks the displayed colouring and every triple of
vertices. The elementary passage from the independent-set bound to the
chromatic lower bound is written here, not formalized in that file.

## No subdivision of K8

Suppose a K8 subdivision existed. Its eight branch vertices are distinct, and
the paths representing its 28 edges have pairwise disjoint internal vertices;
no branch vertex is an internal vertex. Let b_i be the number of branch
vertices in cluster V_i. Then 0<=b_i<=3 and sum_i b_i=8. Only 15-8=7 vertices
are available as internal vertices.

Clusters i and i+2 are nonadjacent. There are b_i*b_(i+2) pairs of branch
vertices of these types. Each representing path needs at least one internal
vertex. A path with exactly one internal vertex requires that vertex to be a
common neighbour of its two endpoints. In this graph such a common neighbour
must belong to cluster i+1. Only 3-b_(i+1) nonbranch vertices in that cluster
are available. The internal-disjointness requirement means at most that many
of the b_i*b_(i+2) paths can have only one internal vertex.

Consequently, paths of this type require at least

    b_i*b_(i+2) + max(0, b_i*b_(i+2) - (3-b_(i+1)))

internal vertices in total. The five unordered types {i,i+2} are distinct and
exhaust the nonadjacent cluster pairs. Summing their internal-vertex counts is
legitimate because all these paths have disjoint internal vertices. Paths
between adjacent branch vertices can only consume additional resources and
may be ignored in a lower bound.

Define

    S = b0*b2 + b1*b3 + b2*b4 + b3*b0 + b4*b1,
    L = S + sum_i max(0, b_i*b_(i+2) - (3-b_(i+1))).

Thus a subdivision implies L<=7. Exhaustive exact arithmetic over all
b_i in {0,1,2,3} with sum_i b_i=8 gives L>=12. There are exactly 155 such
profiles. All are retained in all_155_branch_profiles.csv; the minimum 12 is
attained, for example, at (0,0,2,3,3). Hence 12<=L<=7, a contradiction.

### Small case-split version of the obstruction

One can also use a shorter finite check: either S>=8, which immediately uses
at least eight internal vertices, or, up to rotation and reflection, the
profile is one of the following:

| Profile | S | Additional required internal vertices | Total |
| --- | ---: | ---: | ---: |
| (0,0,2,3,3) | 6 | 6 | 12 |
| (0,1,3,3,1) | 7 | 6 | 13 |

The full arithmetic certificate avoids relying on this symmetry reduction.
The short classification is not an additional Lean theorem in the package.

## Exact reproducibility

Python 3, standard library only:

    python verify.py

This regenerates the complete branch-profile CSV and a JSON report and checks
all 455 unordered triples and the explicit colouring. These checks are not
Lean proof checking.

Lean 4.34.0, bundled Std only (no Mathlib or external solvers required):

    lean Certificate.lean

The Lean certificate uses ordinary `decide`, not native evaluation, and prints
the axiom closures of all six theorem declarations. It introduces no custom
axioms or unfinished proof placeholders. A successful compiler run does not
formalize the prose-only bridges described above.

## References and original-problem boundary

1. Official JSP-000585 catalog:
   https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#jsp-000585
2. Original quantified Erdos 717 statement:
   https://www.erdosproblems.com/717
3. J. Fox, C. Lee, B. Sudakov, Chromatic number, clique subdivisions, and the
   conjectures of Hajos and Erdos-Fajtlowicz, arXiv:1107.1920, published in
   Combinatorica 33 (2013), 181-197:
   https://arxiv.org/abs/1107.1920

The theorem in reference 3 controls chi(G)/sigma(G) by a constant times
sqrt(n)/log(n) (for the relevant n>=2 range). The result above instead gives
one 15-vertex example with chi(G)=8 and sigma(G)<=7. The two statements must
not be conflated.
