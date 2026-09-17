# Verification of the sharp Catlin classification

## Local evidence

The new `Sharp.lean` module compiles under Lean 4.34.0 with warnings treated as
errors. Its three audited endpoints use only `propext`, `Classical.choice`, and
`Quot.sound`. The preceding six proof modules have existing local build evidence.
The expanded Audit.lean checks twelve endpoints, including the exact
classification. Local work uses the previously available Mathlib cache and the
existing executable-path compatibility shim; it is not a fresh dependency build.

## Clean reproduction

Run with the committed toolchain and manifest:

    lake exe cache get
    bash scripts/verify.sh
    bash scripts/verify_nanoda.sh

The Lake library explicitly registers Certificate, GraphCore, Profile,
Subdivision, Colouring, Catlin, and Sharp. This repairs the earlier cloud run's
missing local-module dependency configuration. No proof premise or checking gate
was weakened.

The first verification script builds the entire library with --wfail, replays
all seven proof modules with bundled leanchecker, checks twelve axiom roots,
checks the actual dependency commits against the manifest, and requires rejection
of a false-arithmetic control. The second exports all twelve roots and checks
their transitive closures using pinned lean4export and NaNoda revisions with
strict axiom allowlists. Its checked statements and hashes are archived.

The manifest pins Mathlib to 5ed2965256430c3649e86755f9576b54eca72435.
The automated workflow runs on the catlin-sharp-kz branch. A cloud success is
not asserted in this revision: a separate receipt must record the actual tested
commit, run, check results and artifacts after completion.

Contributor-run checks, including a second kernel implementation, do not provide
independent human semantic review, organizer approval, or an award decision.
