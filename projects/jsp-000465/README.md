# JSP-000465: attributed compactness proof and reproduction package

This package covers the connected-bipartite, non-forest counterexample used by
JSP-000465 / Erdős 575. Its substantive mathematical proof and upstream Lean
formalization already exist. This is a Lean 4.34 compatibility port, a dedicated
problem interface, and a reproducibility contribution. It is not a new solution,
first formalization, or award claim.

## Mathematical statement

There exists a fixed nonempty finite family F of connected bipartite finite
simple graphs, each containing a cycle, such that for every real K > 0,
for all sufficiently large natural n, simultaneously for every H in F,

    K * ex(n,F) < ex(n,H).

Here ex uses ordinary subgraph containment, not induced containment. Therefore
forbidding the entire family cannot be reduced, even within a constant factor,
to forbidding a member. The earlier proof establishes the quantitative bounds
ex(n,F) = O(n^(21/16)) and ex(n,H) = Omega(n^(4/3)). These bounds, including their
construction, are imported from the attributed modules and are not newly claimed.

`JSP000465.lean` proves the simultaneous separation statement and the negative
universal compactness statement. `familyExtremal_singleton` verifies that the
family definition agrees exactly with Mathlib's single-graph extremal number.
`familyExtremal_attained` additionally proves that every extremum has an actual
family-free witness, so the definition does not rely on an empty-set default.
All finite graphs are encoded on `Fin n`, which includes every finite simple
graph up to relabelling. The retained upstream theorem also explicitly proves
connectedness, bipartiteness, and non-acyclicity of every forbidden member.

## Attribution and overlap

- Original mathematical proof and original formalization: OpenAI team / Astra
  (internal OpenAI model), as identified by the source headers.
- Primary publication: Chapter 10, Theorem 1.1, of
  [Ten Advances in Mathematics and Theoretical Computer Science](https://cdn.openai.com/pdf/ten-proofs-oai.pdf).
- Original formal source:
  [openai/ten-proofs, pinned commit](https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean).
- Immediate modular source:
  [plby/lean-proofs, pinned commit](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos180).
  Original headers and Apache-2.0 licensing are preserved. `UPSTREAM_SHA256SUMS`
  fingerprints those seven source files; `PORT.patch` records our compatibility edits.
- This package's port, interface, and verification orchestration were prepared
  under the submitting account with OpenAI ChatGPT/Codex assistance.
- [Official PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) already
  registers the full existing source. It expressly does not independently rebuild
  or kernel-replay third-party dependencies. No priority over that registration
  or its original contributors is claimed here.
- [Official PR #401](https://github.com/TheJustinSunPrize/awards/pull/401) covers
  a separate unrestricted example involving forests and a disconnected member.
  This package retains the connected-bipartite non-forest conditions.

## Reproduction

The pinned compiler and package revisions are in `lean-toolchain` and
`lake-manifest.json`. With the pinned toolchain and dependencies available:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as errors, replays all eight local
modules with the bundled checker, audits seven named theorem closures, checks the
actual dependency Git revisions, and requires a false arithmetic claim to fail.
The second exports those closures and checks them with the pinned NaNoda
implementation with a strict three-axiom allowlist. A successful contributor-run
check is not an independent human review or organizer approval.

Verification results will be recorded only after the runs finish. The workflow
retains logs, statements, source, dependency versions, and checker exports in a
GitHub Actions artifact with finite retention. No permanent external archive or
cash entitlement is asserted.
