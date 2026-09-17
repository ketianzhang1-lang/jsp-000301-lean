# Exact statement correspondence

The reference is Formal Conjectures commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`,
[`FormalConjectures/ErdosProblems/1142.lean`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1142.lean).

`JSP000947.Good` has exactly the same body as `Erdos1142.Erdos1142Prop`:

```lean
2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime
```

`JSP000947.mientka_weitzenkamp` proves the exact set equality in
`Erdos1142.erdos_1142.variants.mientka_weitzenkamp`. The reference marks that
variant as research solved but leaves its proof as a placeholder at the
pinned revision. This standalone project does not import that placeholder.
`Audit.lean` checks the theorem against the fully expanded original
predicate, independently of the `Good` abbreviation in the displayed type.

The upper bound is inclusive, the exponent ranges over every positive
natural number with 2^k < n, and n > 2 excludes the vacuous cases 0, 1, 2.
There are no extra hypotheses or axioms restricting n. Both directions of
the equality are proved. The separate unrestricted infinitude question
`Erdos1142.erdos_1142` is not resolved or changed by this work.
