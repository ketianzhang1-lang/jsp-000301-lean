# Verification record

Local check date: 2026-09-17.

- Lean 4.34.0 compiled all seven modules with `warningAsError=true`.
- Bundled `leanchecker` replayed `Adapter` and `Audit` successfully.
- All five exported theorem axiom lists contain only `propext`,
  `Classical.choice`, and `Quot.sound`; no placeholder axiom occurs.
- The proof uses no `sorry`, `admit`, `native_decide`, or new axioms.
- Source hashes and compiler/kernel logs are in `evidence/`.

The local run used the preinstalled Mathlib cache and a compiler-launch
compatibility wrapper. The cache has incomplete git metadata, so the local
dependency revision check could not establish all checkout hashes. A clean
CI run with the pinned manifest is needed for that additional check.

The NaNoda reproduction script is supplied, but no NaNoda success is claimed
until its run is recorded. These are contributor-run checks, not an
independent human review or an award decision. Any later CI result must be
associated with its exact tested commit.
