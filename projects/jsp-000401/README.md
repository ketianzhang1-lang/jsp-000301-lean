# JSP-000401: the classical Turán 5/9 lower bound

This package formalizes a known lower bound for the tetrahedron-free three-uniform hypergraph problem. It is a partial contribution to JSP-000401, not a solution of the open extremal problem.

## Exact result

For every natural number n, including 0, 1 and 2, there is a finite simple three-uniform hypergraph E on exactly the vertex type Fin n such that E contains no complete three-uniform hypergraph on four distinct vertices and

    5 * choose(n, 3) <= 9 * |E|.

Equivalently, ex(n, K_4^(3)) is at least ceil(5 * choose(n, 3) / 9). The package does not establish the conjectural matching upper bound or optimality of a balanced partition. It does not formalize existence of the limiting Turán density; its all-n finite bound is the standard lower-bound input for that theory.

The endpoint is `JSP000401.turan_lower_bound`. `Valid E` explicitly states three-element edges and exclusion of all four three-element subsets on any four pairwise distinct vertices. Edges are `Finset (Finset (Fin n))`, so repetitions and vertices outside Fin n are impossible. The exclusion is of a subhypergraph, not merely an induced subhypergraph.

## Mathematical argument

Use three colors, cyclically numbered 0, 1, 2. Keep a triple if its colors are all distinct, or if two vertices have color i and the remaining vertex has color i+1 modulo three. This is Turán's classical cyclic construction.

No four vertices span a tetrahedron. If at least three have the same color, those three are not an edge. Otherwise the color multiplicities are 2+2 or 2+1+1. In the former case the two opposite cyclic orientations cannot both be allowed. In the latter case one of the triples using the repeated color has the disallowed singleton color. The Lean theorem `no_four` verifies the finite color statement by kernel reduction.

Exactly 15 of the 27 colorings of an ordered triple are allowed: six have all distinct colors; nine consist of a repeated color, its cyclic successor, and one of three singleton positions. For any fixed three-element subset, the remaining n-3 vertex colors are unrestricted. Thus it is retained by exactly 15 * 3^(n-3) colorings when n>=3. `edge_frequency` proves this by a bijection separating the three vertices from their complement. `good_permutation` and `goodSet_iff` ensure the count is independent of the chosen enumeration.

Double-count edge-coloring incidences. The sum of edge counts over all 3^n colorings is choose(n,3) * 15 * 3^(n-3). At least one coloring therefore has 9|E|>=5 choose(n,3). Orders below three are handled separately.

## Attribution and overlap

Mathematical credit belongs to Paul Turán. The construction and 5/9 lower bound are described in Peter Keevash, *Hypergraph Turán Problems*, Section 7, printed page 18:

https://people.maths.ox.ac.uk/keevash/papers/turan-survey.pdf

Official problem record:

https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000401

The proof implementation was written for `ketianzhang1-lang` with OpenAI ChatGPT assistance. It uses Mathlib's finite-set, equivalence, summation and arithmetic infrastructure. It does not copy a third-party solution file. No new mathematical discovery or globally first formalization is claimed.

On 2026-09-17, searches of the official issues and pull requests for `JSP-000401` and `tetrahedron` returned no matches. A search for `Erdos500` in `plby/lean-proofs` returned none. These are limited searches, not a priority guarantee; the official JSP identifier is the scope identifier used here.

The catalog is Open / Lean No / Eligible No. A request to review this partial formalization does not override that status or establish any award eligibility or payment entitlement. The historical $500 bounty in the catalog must not be treated as a reward for this known lower bound.

## Reproduce

Lean is pinned to v4.34.0. The manifest fixes Mathlib to 5ed2965256430c3649e86755f9576b54eca72435 and records all transitive dependency revisions.

    lake exe cache get
    bash scripts/verify.sh
    bash scripts/verify_nanoda.sh

`verify.sh` compiles with warnings as errors, replays the compiled module with the bundled Lean checker, audits nine named declarations against the allowlist propext / Classical.choice / Quot.sound, checks dependency revisions, and rejects a false-arithmetic negative control. The proof uses kernel-reduced `decide`, not `native_decide` or compiler-trust axioms.

`verify_nanoda.sh` builds pinned lean4export and NaNoda implementations and checks the dependency closures of the endpoint and total-incidence theorem. It allows only the same three foundational axioms. This is an independently implemented checker run by the contributor; it is not independent human review or organizer certification. It requires Git, network access and a Rust toolchain.

The public workflow archives the tested source, logs and checker export. GitHub Actions artifacts have finite retention; fixed Git commits preserve the source. See VERIFICATION.md for actual results and their limits.

## License

The new source and documentation are offered under Apache-2.0, consistently with the proof repository. Mathlib and all fetched checking tools retain their own licenses and attribution.
