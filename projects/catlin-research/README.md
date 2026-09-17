# Complete formal proof of the known Catlin counterexample

The endpoint `CatlinComplete.catlin_counterexample` proves that the explicit
15-vertex graph C5[K3] has chromatic number exactly 8 and has no subdivision
of K8. The paths, their simplicity, disjoint interiors, and avoidance of
branch vertices are expressed using actual Mathlib graph walks.

This completes the two graph-theoretic bridges absent from the earlier
finite-certificate checkpoint at commit
`96ca7edd443f661da2b5763bc1a5834533968c21`.

**Scope:** this is a complete formal proof of the known finite Catlin
counterexample to Hajos's conjecture. It is only a related, scoped component
for JSP-000585 / Erdos 717. It does not prove the original uniform asymptotic
bound over all finite graphs. Mathematical credit remains with Catlin;
no new mathematics or worldwide first-formalization priority is claimed.
The extension was written with OpenAI ChatGPT assistance.

## Proof modules

- `Certificate.lean`: inherited exact finite graph and arithmetic certificates.
- `GraphCore.lean`: the graph, genuine walk interiors, and path-length bounds.
- `Profile.lean`: five-cluster partition, a finite certificate, and its connection to arbitrary branch sets.
- `Subdivision.lean`: faithful subdivision definition and the disjoint-interior counting bound.
- `Colouring.lean`: proper 8-colouring, impossibility of 7 colours, and exact chromatic number.
- `Catlin.lean`: the final contradiction and combined endpoint.
- `Audit.lean`: nine target axiom audits.

See `PROOF.md` for the mathematical argument and statement boundary,
`VERIFICATION.md` for actual checks and their limits, and `scripts/` for
reproduction. Historical finite-enumeration support remains in `verify.py`.
