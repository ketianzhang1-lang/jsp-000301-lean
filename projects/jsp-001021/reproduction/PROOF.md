# Independent proof that every 15-vertex tournament contains a transitive 5-set

This document preserves our independent mathematical reconstruction. The local exclusions and final ordered witness are now checked in `../FiniteChecks.lean`. The complete main Lean proof in `../JSP001021.lean` uses the separately attributed fourteen-vertex theorem, followed by our restriction and transport lemmas; it is not presented as a formalization of every step of this independent reconstruction.

Let `TT_k` denote a transitive tournament on `k` vertices. For a tournament `T`, write `N+(v)` and `N-(v)` for the out- and in-neighbourhoods of `v`.

The goal is to prove that every tournament on 15 vertices contains `TT_5`. This is enough to refute the formula proposed in Erdős Problem 1216 at `n = 15`, because `floor(log2 15) + 1 = 4`.

## 1. The seven-vertex model

Let the vertex set be `Z/7Z`, let `Q = {1,2,4}`, and orient

`i -> j` iff `j - i (mod 7)` belongs to `Q`.

Call this tournament `P`. Every vertex has outdegree and indegree 3. For each `i`, both its out-neighbourhood `O_i` and its in-neighbourhood `I_i` are directed 3-cycles. In particular `P` has no `TT_4`: a source of a transitive 4-set would need three out-neighbours spanning a transitive triple, but each out-neighbourhood is a directed triangle.

There are exactly 14 cyclic triples in `P`, namely the seven `O_i` and seven `I_i`. Indeed every transitive triple has a unique source, so the number of transitive triples is `7 * C(3,2) = 21`; out of `C(7,3)=35` triples, the remaining 14 are cyclic.

## 2. Classification of seven-vertex tournaments without TT_4

**Lemma 1.** Every seven-vertex tournament containing no `TT_4` is isomorphic to `P`.

Every tournament on four vertices contains a transitive triple: some vertex has outdegree at least 2, and together with two of its out-neighbours it forms a transitive triple. Hence, in a seven-vertex tournament without `TT_4`, every vertex has outdegree and indegree at most 3. Since the two degrees sum to 6, every vertex has both degrees exactly 3.

Fix a vertex `v`. Let `A={a0,a1,a2}=N+(v)` and `B={b0,b1,b2}=N-(v)`. Both `A` and `B` must be directed 3-cycles. Number them cyclically. Each `a_i` has one win inside `A` and loses to `v`, so it must beat exactly two vertices of `B`; equivalently it loses to exactly one `b_j`. Dually each `b_j` beats exactly one `a_i`. Thus the three edges from `B` to `A` form a perfect matching, represented by a permutation `pi`.

After rotating the labels in `B`, assume `pi(0)=0`. The remaining possibilities are equivalent to two cases. One produces a `TT_4` immediately; in the other, the map

`(v,a0,a1,a2,b0,b1,b2) -> (0,1,2,4,6,3,5)`

is an isomorphism to `P`. The included checker verifies all six permutations directly and finds exactly the isomorphic/non-isomorphic cases asserted above.

A useful consequence in `P` is that any two distinct vertices have exactly one common out-neighbour.

## 3. Assume a 15-vertex counterexample

Suppose a tournament `T` on 15 vertices contains no `TT_5`.

Every tournament on 8 vertices contains a `TT_4`: some vertex has at least four out-neighbours, those four contain a transitive triple, and adjoining the source gives a transitive 4-set. Therefore no vertex of `T` can have outdegree or indegree at least 8, since a `TT_4` in that neighbourhood would extend to a `TT_5`. As the two degrees sum to 14, every vertex has outdegree and indegree exactly 7.

Fix `v`, put `A=N+(v)` and `B=N-(v)`, and identify `B` with the model `P`, labelled `B_0,...,B_6`. Every seven-vertex out- or in-neighbourhood is `TT_4`-free and hence isomorphic to `P` by Lemma 1.

For each `a in A`, define

`C_a = { j : B_j -> a }`.

Inside `A`, the vertex `a` has three wins; it loses to `v`; and in the whole tournament it has seven wins. Hence it has four wins and three losses against `B`, so `|C_a|=3`.

Moreover `C_a` must be a directed triangle in `B`. If `C_a` contained a transitive triple, then those three vertices followed by `v,a` would form a `TT_5`. Since the cyclic triples of `B` are exactly the `O_i` and `I_i`, every `C_a` belongs to `{O_0,...,O_6,I_0,...,I_6}`.

## 4. Pair intersection lemma

**Lemma 2.** For distinct `a,a' in A`, `|C_a intersection C_a'| = 1`.

Assume `a -> a'`. In the seven-vertex tournament `N+(a)`, which is a copy of `P`, the vertex `a'` has outdegree 3. Thus `a` and `a'` have exactly three common out-neighbours in `T`. They have exactly one common out-neighbour inside `A`, by the corresponding property of `P`, and neither points to `v`. Hence they have exactly two common out-neighbours in `B`.

Those common out-neighbours are precisely `B \ (C_a union C_a')`. Therefore

`2 = 7 - |C_a union C_a'| = 7 - (3+3-|C_a intersection C_a'|)`,

so the intersection has size 1.

## 5. The local two-vertex exclusion

Take `a,b in A` with `a -> b`. The local tournament on `B union {v,a,b}` is determined by `B`, the edges `B -> v -> a,b`, the edge `a -> b`, and the two cyclic triples `C_a,C_b`.

**Lemma 3.** If this local tournament has no `TT_5` and `|C_a intersection C_b|=1`, then only the following patterns can survive:

1. `(C_a,C_b)=(O_i,I_j)` with `i -> j` in `P`; or
2. `(C_a,C_b)=(I_i,I_j)` with `j -> i` in `P`.

The proof is finite. Affine maps `x -> r*x+t` with `r in {1,2,4}` are automorphisms of `P`, so the first index may be normalized to 0 and the second to one of `0,1,3`. This leaves 12 normalized cases. Cases with intersection size different from 1 are excluded by Lemma 2; among the remaining cases, explicit `TT_5` witnesses eliminate all but the two pattern families above.

The included `verify.py` performs the stronger exhaustive check over all `14*14=196` ordered pairs of cyclic triples, not merely the 12 normalized representatives, and confirms exactly the same survivors.

A key consequence is that the second set `C_b` in every oriented edge `a -> b` must be an `I_j`.

## 6. Global forcing and contradiction

Every vertex of the seven-vertex tournament `A` has an in-neighbour. Given any `a in A`, choose `a'` with `a' -> a`. By Lemma 3, `C_a` must therefore be one of the seven `I_j`.

Distinct vertices of `A` give distinct `C_a`, since equal sets would intersect in three points, contradicting Lemma 2. Hence we may relabel the vertices of `A` as `A_0,...,A_6` so that

`C_{A_i}=I_i`.

Lemma 3 then forces the orientation inside `A` to be the reverse of the orientation inside `B`:

`A_i -> A_j` iff `B_j -> B_i`.

The cross edges are also fixed:

`B_j -> A_i` iff `B_j -> B_i`,

and

`A_i -> B_j` iff `i=j` or `B_i -> B_j`.

Now the ordered five vertices

`(A_0, B_1, A_5, B_2, A_3)`

form a `TT_5`. The ten required forward edges reduce to differences modulo 7 lying in `Q={1,2,4}`:

- `A0 -> B1` from `B0 -> B1` (difference 1),
- `A0 -> A5` from `B5 -> B0` (difference 2),
- `A0 -> B2` from `B0 -> B2` (difference 2),
- `A0 -> A3` from `B3 -> B0` (difference 4),
- `B1 -> A5` from `B1 -> B5` (difference 4),
- `B1 -> B2` (difference 1),
- `B1 -> A3` from `B1 -> B3` (difference 2),
- `A5 -> B2` from `B5 -> B2` (difference 4),
- `A5 -> A3` from `B3 -> B5` (difference 2),
- `B2 -> A3` from `B2 -> B3` (difference 1).

This contradicts the assumption that `T` contains no `TT_5`. Therefore every 15-vertex tournament contains a transitive 5-vertex subtournament.

## 7. What this does and does not establish

This is a full mathematical counterexample to the *universal proposed formula*: one value of `n` where the guaranteed transitive size exceeds the proposed value is sufficient to refute the universal equality. It does not determine the exact extremal function for every `n`.

It is not new mathematics. Reid and Parker proved the stronger 14-vertex statement in 1970, and a public complete Lean formalization of that stronger statement already exists in `plby/lean-proofs` at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, file `src/latest/ErdosProblems/Erdos1216.lean`.

The Python checker is a finite consistency/reproduction aid only. It is not a Lean proof and does not replace independent mathematical review.
