# Original statement correspondence

JSP-000907 is Erdős Problem 1091. The two original questions are represented
without replacing either by a special case.

| Original object or quantifier | Formal representation |
| --- | --- |
| Arbitrary finite simple graph | `SimpleGraph V`, `[Fintype V]`; catalog endpoint uses every `Fin n` |
| Chromatic number exactly four | `G.chromaticNumber = (4 : ENat)` |
| K4-free | Mathlib `G.CliqueFree 4` |
| Odd simple cycle | A closed walk `p`, `p.IsCycle` and `Odd p.length` |
| Chord | Mathlib `Walk.IsChord`, an ambient edge between cycle vertices absent from the cycle edge list |
| Number of chords | `Erdos1091.Walk.chordCount`, a finite set of unordered edges, so neither orientation nor multiplicity is double-counted |
| Every subgraph on at most r vertices | `SmallSubgraphsThreeColorable G r`, using every `G.Subgraph` and `H.verts.ncard <= r` |
| Equivalence to upstream local hypothesis | `smallSubgraphs_iff_induced` proves both directions, including subgraphs formed by deleting edges |
| Quantitative threshold | Arbitrary `f : Nat -> Real`; no integrality or monotonicity is assumed |
| Tends to infinity | `Filter.Tendsto f atTop atTop` |
| Complete endpoint | `JSP000907.jsp_000907` |

`affirmative` transports the full upstream affirmative proof to arbitrary
finite vertex types. `explicit_counterexample` supplies, for every r, a
K4-free four-chromatic graph with r < n <= r+31 whose small subgraphs are
three-colorable and whose every cycle has at most ten chords. All of these
properties come from the fully proved APSSV source; choosing m=floor(r/20)
establishes the displayed order bounds.

`realGuarantee_le_ten` proves a pointwise obstruction at every r. The
no-divergence conclusion follows for real functions, and even an unbounded
range is impossible. Thus the negative half is not restricted to a single
r, a subsequence, integer-valued thresholds or monotone functions.

Our own odd-rim family is separate from the APSSV family. Its formalized
properties are its exact order, exact chromatic number and explicit
nine-cycle with at least four chords. Its informal universal four-chord
upper bound and criticality are not used by the complete endpoint.

The permitted logical axioms are the standard `propext`, `Classical.choice`
and `Quot.sound`. No omitted combinatorial result is supplied as an axiom or
as an extra hypothesis of the complete endpoint. Machine verification and
human assessment of this correspondence remain distinct.
