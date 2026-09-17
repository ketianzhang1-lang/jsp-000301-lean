# JSP-000438 / Erdős 547: the full tree Ramsey upper bound

This project proves, for **every** `n ≥ 2` and every tree `T` on `Fin n`,

\[
R(T,T)\le 2n-2.
\]

The main declaration is `Erdos547.erdos_547` in [JSP000438.lean](JSP000438.lean).
It has the same universal statement and Ramsey definitions as the cited
Formal Conjectures target. It is not restricted to sufficiently large trees,
bounded degree, bounded diameter, or a particular family of trees.
The direct coloring theorem also proves that the defining Ramsey set is nonempty.

The major mathematical dependency is an **existing public proof**, reproduced
with credit and license: `Erdos548.tree_free_edge_bound` from
[tadamcz/erdos548 at 82ffb751f3d37768927df9239ed08439bbe0dd09](https://github.com/tadamcz/erdos548/tree/82ffb751f3d37768927df9239ed08439bbe0dd09).
This submission contributes a Lean 4.34 port, the all-order Ramsey deduction,
statement alignment, and reproducible checks. It does **not** claim authorship
of the Erdős–Sós proof or discovery of the mathematical implication, nor
first-formalization priority. OpenAI Codex assisted the new work.
See [UPSTREAM_PORT.md](UPSTREAM_PORT.md) and [NOTICE](NOTICE).

## Proof

Put `N = 2n-2`. If neither a graph `G` on `N` vertices nor its complement
contains `T`, the credited tree-free edge bound gives

\[
2e(G)\le(n-2)N,\qquad 2e(\overline G)\le(n-2)N.
\]

But `e(G)+e(\overline G)=N(N-1)/2`, so these inequalities imply
`N(N-1) ≤ (2n-4)N`. Since `N > 0` and `N-1 = 2n-3`, this is impossible.
The code first proves the asymmetric version `R(T,S) ≤ m+n-2` for trees of
orders `m,n ≥ 2`, and then specializes it to the stated diagonal bound.

The dependency is the **sharp internal** tree-free inequality, not merely
the upstream terminal theorem with an extra half-edge margin for some parities.
No density theorem is postulated as an axiom or left as a hypothesis.

## Declarations and interfaces

| Declaration | Content |
| --- | --- |
| `Erdos548.tree_free_edge_bound` | Credited upstream all-order extremal bound |
| `JSP000438.trees_monochromatic` | Direct asymmetric red/blue containment statement |
| `JSP000438.tree_monochromatic` | Direct diagonal statement for every `n ≥ 2` |
| `JSP000438.graphRamsey_trees` | Asymmetric Ramsey-number bound |
| `Erdos547.erdos_547` | Exact full universal target |

`SimpleGraph.IsContained` is injective subgraph containment, not induced
containment. A coloring is represented by `G` and its actual graph complement.
[STATEMENT.md](STATEMENT.md) explains the alignment and coverage.

## Reproduce

Use Lean `leanprover/lean4:v4.34.0` and the committed `lake-manifest.json`.
Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as errors, replays the module
with the bundled Lean checker, checks five axiom closures and every actual
dependency revision, and requires a false arithmetic statement to be rejected.
The second exports all five targets with their dependencies and checks them
with the pinned NaNoda implementation, using a hard-error axiom allowlist of
`propext`, `Classical.choice`, and `Quot.sound`.

The workflow `.github/workflows/jsp-000438.yml` saves the checked source,
manifest, export, logs, and checksums in its evidence artifact. A successful
machine run is evidence about the formal proof, not an award decision or an
independent human review. The formalization contribution and upstream credit
remain subject to organizer review.

## License

Apache-2.0. The original dependency, its unchanged reference source, copyright,
NOTICE, and README are retained. The Ramsey definitions retain the Formal
Conjectures Authors' copyright and are extracted under the same license.
