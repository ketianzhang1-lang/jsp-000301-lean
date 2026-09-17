# Statement alignment and scope

## Original formal target

The target is `Erdos547.erdos_547` in
[FormalConjectures/ErdosProblems/547.lean](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/547.lean):

```lean
∀ (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)),
  T.IsTree → SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2
```

The declaration in this project has exactly this type. Only the project-specific
research category / AMS metadata is omitted. `Audit.lean` applies the proved
theorem to this explicit type.

The `graphRamsey` and `diagonalGraphRamsey` definitions are extracted verbatim
from the same pinned Formal Conjectures repository. The former is the natural
infimum of host orders such that every graph contains the first target or its
complement contains the second target. The latter specializes to identical
targets. The full large repository, including its unproved statements, is not
an imported dependency of this standalone project.

## Coverage

- All natural tree orders `n ≥ 2`, including `n = 2`.
- All finite simple trees on `Fin n`, using Mathlib's `IsTree`.
- All graphs on exactly `2n-2` vertices and their actual complements.
- Non-induced injective subgraph containment, using Mathlib's `IsContained`.
- No threshold of sufficiently large `n`, no degree restriction, and no
  unproved extremal hypothesis in the final theorem.

The direct theorem supplies a witness for the Ramsey set, so the result does
not exploit the natural infimum's value on an empty set. Orders zero and one
are outside the explicit target; the `n = 1` inequality `R(T,T) ≤ 0` would
not be the intended statement. This is an upper bound, not a formula for the
exact Ramsey number of every individual tree.

## Dependency fidelity

The proof uses the complete public Erdős–Sós development's internal theorem:

```lean
Erdos548.tree_free_edge_bound
  (T : SimpleGraph U) (hT : T.IsTree) (ht : 2 ≤ Fintype.card U)
  (G : SimpleGraph V) (hn : 0 < Fintype.card V) (hfree : ¬T.IsContained G) :
  2 * G.edgeSet.ncard ≤ (Fintype.card U - 2) * Fintype.card V
```

This exact inequality handles all parities. Its complete proof is in the
compiled source; the downstream theorem does not merely assume Erdős–Sós.
The modified source and its unmodified original are distinguished, attributed,
and linked by a complete patch and hashes.

## Prior work and review limits

At the checked official catalog commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`, JSP-000438 is recorded as
Open / Lean proof No / Eligible to claim No; JSP-000439 already credits the
public Erdős–Sós result and formalization. The catalog status is a review
record, not evidence that the mathematical implication is new.

The consulted `plby/lean-proofs` snapshot
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e` includes the sufficiently-large
result and a conditional reduction for Erdős 547. Official issue/PR searches
for JSP-000438 found no match during preparation. These searches are not an
exhaustive proof of priority. This submission asks for review of the concrete
port and full-statement integration; it does not nominate the submitter as
the solver of the credited upstream mathematics.
