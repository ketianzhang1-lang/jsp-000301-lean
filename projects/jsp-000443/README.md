# JSP-000443 / Erdős 552: C4 versus star Ramsey bounds

**Partial scope. This package does not solve the original all-parameter problem
or its unbounded-deficit question, and does not establish award eligibility.**

It independently formalizes elementary, known graph-theoretic bounds and a
known infinite family of exact values. Mathematical novelty and first-formalization
priority are not claimed.

## Checked mathematical targets

Write `R(C4,K1,n)` for the least number of vertices such that every red/blue
edge coloring contains a red four-cycle or a blue star with **n leaves**
(n+1 vertices). Copies are ordinary subgraphs, not induced subgraphs.

- For every natural n, `R(C4,K1,n) <= n + floor(sqrt(n)) + 2`.
- For every positive even k, `R(C4,K1,k^2) <= k^2 + k + 1`.
- For every integer r > 0, with q = 2^r, `R(C4,K1,q^2) = q^2 + q + 1`.
- In particular: `R(C4,K1,16) = 21`, `R(C4,K1,64) = 73`, and `R(C4,K1,256) = 273`.

The formal `c4StarRamsey` is the least N satisfying that property, using
`Nat.find` with its existence supplied by the proved universal upper bound.
Theorems `hasC4_iff_copy` and `hasStar_iff_copy` establish equivalence with
Mathlib's `SimpleGraph.Copy`, `cycleGraph 4`, and
`completeBipartiteGraph (Fin 1) (Fin n)`.

## Proof

In a C4-free graph, second-step neighbors reached through distinct first-step
neighbors of a root are disjoint, once the root is erased. Minimum degree d
therefore gives `degree(v)*(d-1) <= N-1`. If the complement has no n-leaf
star, every original degree is at least N-n. The square-root bound follows.

At N=k^2+k+1 and n=k^2, equality forces every degree to equal k+1. For
positive even k this would be an odd-regular graph of odd order, contrary
to the degree-sum identity. This proves the improvement by one vertex.

For the lower bound at n=16, a 20-vertex graph has minimum degree 4 and
no four-cycle. Its complement has maximum degree at most 15. The graph
comes from orthogonality of projective points over GF(4), deleting one
absolute point. The Lean kernel checks its literal adjacency rows,
symmetry, absence of loops, all codegrees, and degree bound. The Python
generator is reproducibility support, not a trusted proof oracle.

The module `PolarityFamily.lean` proves a uniform algebraic construction
over an arbitrary finite field, replacing reliance on isolated adjacency
tables for the infinite family. See [FAMILY_PROOF.md](FAMILY_PROOF.md).

## Attribution and scope

- [Original problem / current catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000443).
- [Formal Conjectures statement of Erdős 552](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/552.lean).
- T. D. Parsons, *Ramsey graphs and block designs I*, Transactions of the
  American Mathematical Society **209** (1975), 33–44: classical background
  for C4/star bounds and projective-plane constructions. This package does
  not claim all bounds or constructions in that paper.
- S. Burr, P. Erdős, R. J. Faudree, C. C. Rousseau and R. H. Schelp,
  *Some complete bipartite graph-tree Ramsey numbers* (1989), 79–89:
  the original problem reference recorded by Formal Conjectures.

The Lean implementation and finite GF(4) generator were written with
OpenAI ChatGPT assistance under the submitting account's direction.
No third-party solution file was copied or imported; Mathlib supplies the
general mathematical infrastructure. Proposed formalization contributor
placeholder, if relevant: `RECIPIENT-JSP-000443-KZ-A`, confirmation pending.

The catalog currently marks the whole problem **Progress / Lean No /
Eligible No / Unavailable**. These results do not change that status.
The exact n=16 theorem, all-n upper bound and even-square family are
components, not a complete formula. In particular, they do not prove
that for every c>0 there are infinitely many n with R <= n+sqrt(n)-c.

## Reproduction

Pinned Lean 4.34.0; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; transitive dependency revisions
are fixed in `lake-manifest.json`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings as errors, replays the main module
with Lean's bundled checker, audits sixteen declarations, checks dependency
revisions, rejects a false-arithmetic negative control, and reproduces
the finite adjacency rows. The second exports six endpoint dependency
closures and checks them with pinned NaNoda under a strict allowlist of
`propext`, `Classical.choice`, and `Quot.sound`.

Successful contributor-run checks are distinct from independent human
review, organizer acceptance, award allocation, and payment approval.
See `VERIFICATION.md` for observed results rather than treating these
reproduction instructions as evidence that a command has already run.
