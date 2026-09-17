# JSP-000438 / Erdős 547: the full tree Ramsey upper bound

## Our formalization contribution

We provide the **complete tree Ramsey formalization**, with OpenAI Codex assistance. We prove, for every `n ≥ 2` and every tree `T` on `Fin n`,

\[
R(T,T)\le 2n-2.
\]

Our contributions in this version are:

1. **Full Ramsey integration.** We formalize the asymmetric bound `R(T,S) ≤ m+n−2` for arbitrary trees of orders `m,n ≥ 2`, then derive the complete universal Erdős 547 statement.
2. **Exact statement alignment.** We use the stated Ramsey definitions and prove direct injective containment theorems, including nonemptiness of the defining Ramsey sets.
3. **Finite-color extension.** We formalize the bound `R(T_1,...,T_r) ≤ 2 + sum_i (|T_i|-2)` for every finite nonempty family of trees of order at least two, together with a direct monochromatic embedding theorem.
4. **Lean 4.34 compatibility.** We port the required extremal-tree dependency to the pinned Lean/Mathlib environment and document the changes.
5. **Reproducible verification.** We supply locked dependencies, build scripts, Lean checker replay, axiom audits, a negative control and NaNoda verification.

Our main declaration is `Erdos547.erdos_547` in [JSP000438.lean](JSP000438.lean). It covers every required tree order with the same universal statement and Ramsey definitions as the Formal Conjectures target.

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

## Finite-color supplement

[Multicolor.lean](Multicolor.lean) now extends the Ramsey integration to every
finite family of trees: `R(T_1,...,T_r) ≤ 2 + sum_i (|T_i|-2)`.
It proves both a graph-cover statement and a direct injective monochromatic
embedding for an actual edge coloring. See [MULTICOLOR.md](MULTICOLOR.md) for
the exact scope, proof, and attribution. The mathematical implication is known;
this addition contributes its formal integration and verification.

## Reproduce

Use Lean `leanprover/lean4:v4.34.0` and the committed `lake-manifest.json`.
Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as errors, replays the module
with the bundled Lean checker, checks nine axiom closures and every actual
dependency revision, and requires a false arithmetic statement to be rejected.
The second exports all nine targets with their dependencies and checks them
with the pinned NaNoda implementation, using a hard-error axiom allowlist of
`propext`, `Classical.choice`, and `Quot.sound`.

The workflow `.github/workflows/jsp-000438.yml` saves the checked source,
manifest, export, logs, and checksums in its evidence artifact. A successful
machine run is evidence about the formal proof, not an award decision or an
independent human review. The formalization contribution and upstream credit
remain subject to organizer review.

## Contribution scope and attribution

We request formalization credit for our Ramsey integration, finite-color proofs, compatibility port and verification work. The mathematical implications and constructions are classical.

Our upper-bound proof uses an existing formal Erdős–Sós edge bound. We retain the dependency's source attribution and license, together with the Formal Conjectures attribution; details are in [UPSTREAM_PORT.md](UPSTREAM_PORT.md) and [NOTICE](NOTICE).

## Verification record

Our [successful public verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177218300) checks proof snapshot `0175b2a7a50f7687ece92f61bbe0e3a2f377913a`. This README revision changes documentation only; the Lean proofs, dependencies, verification scripts and workflows are unchanged.

## License

Apache-2.0. The original dependency, its unchanged reference source, copyright,
NOTICE, and README are retained. The Ramsey definitions retain the Formal
Conjectures Authors' copyright and are extracted under the same license.
