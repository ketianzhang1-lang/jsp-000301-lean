# Verification evidence: JSP-000391

These are contributor-run results for the stated general-base construction, not organizer approval, independent human certification, or an award decision.

## Exact tested source

- Repository: `ketianzhang1-lang/jsp-000301-lean`.
- Proof commit: **`56f083c6183e93eeffc334e04e39a26548bfae96`**.
- Directory: `projects/jsp-000391`.
- [Successful public run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35157931469): run 3, job `105001695072`, September 16, 2026.
- Lean **4.34.0**, compiler commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib **`5ed2965256430c3649e86755f9576b54eca72435`**. All nine dependency revisions are committed and checked against their actual Git checkout revisions.
- The seven Lean/audit/build/manifest/license files listed in `SOURCE_SHA256SUMS` are unchanged from this successful source revision. This receipt and the compact logs were preserved in the original PR and are now included in the proof repository. The development README at the tested commit predates completed verification; the current README corrects that status. The documentation-only descendant changes no proof, dependency, script or workflow input. The original CI result is evidence for the listed tested commit, not a claim that CI has run on every subsequent documentation commit.

## Observed results

`lake build --wfail` passed, **8,927 jobs**, compiling both `JSP000391` and `JSP000391Main`. These are total build-graph jobs, not 8,927 newly written proofs. The target source files were actually compiled.

Both `lake env leanchecker JSP000391` and `lake env leanchecker JSP000391Main` passed. This reuses the Lean kernel implementation; it is not a second implementation.

All **eight** printed target axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. They include `stoll_general_base`, `jsp000391`, normalization, digit bounds, and reconstruction/convergence. Actual reports are included in [evidence/axioms.log](evidence/axioms.log).

The same pipeline rejected the deliberately false arithmetic proposition `1=0`. This is a limited negative-control sanity check, not a general soundness theorem. A separate exact rational cross-check passed 300 parameter triples and 6,000 digit tests; the numerical tests are not a proof dependency and do not replace universal quantifiers.

**NaNoda 0.4.17**, pinned at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, returned:

```text
Checked 17401 declarations with no errors
```

The exporter was `leanprover/lean4export@6cea97789dc088ea47fcea15692db85685aedac5`, built with the same Lean toolchain. Target selection included the universal final theorem, explicit-shift corollary, digit bounds, subsequence closed forms and multiplier correspondence, with their complete transitive dependency closures. The configuration permits only the standard three axioms and has `unpermitted_axiom_hard_error: true`. No compiler-trust or native-evaluation axiom is permitted. Pretty-printing the definitions and final theorem statements also completed without errors. The original transcript and checker export are retained in the artifact.

## Artifact integrity

[Artifact 10471333076](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35157931469/artifacts/10471333076), `jsp-000391-evidence`, **12,170,425 bytes**.

ZIP SHA-256: **`ed182bb56a1e1f3986c65593f428afd9df1bcd71a3005895a74a1fd2fb1912ca`**.

The artifact was downloaded and its ZIP hash checked before extracting the original submission files. It includes the source snapshot, build, kernel replay, axiom, negative-control and NaNoda logs, checker configuration, pretty-printed statements, compressed proof export and manifest. Hashes for the source archive and compressed checker export are inside the original artifact. The seven proof/configuration files have independent hashes in `SOURCE_SHA256SUMS`.

GitHub reports expiration on **December 15, 2026**. This is finite-retention evidence, not independent permanent archival. A local backup is also available to the submitting contributor. The public source remains pinned to a Git commit.

## Remaining review boundaries

The contributor operated both implementations using AI-assisted tooling. Network access and official cached Mathlib build artifacts were used; a network-disabled, from-source rebuild of all Mathlib is not claimed. No independent human signature, organizer-approved minimum-safe-version finding, award tier, confirmed recipient identity, global priority determination, or payment entitlement is asserted. The formal scope is Stoll's complete Theorem 1.3 construction and supporting correctness properties, not every related statement in the literature.
