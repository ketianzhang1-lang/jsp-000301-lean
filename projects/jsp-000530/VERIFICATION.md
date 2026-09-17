# Verification receipt

## Exact proof source

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Commit: `fb8577233935d1ff4533418ff8ea33a4d7dab101`
- Directory: `projects/jsp-000530`
- Workflow: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169007348
- Job: `105036383618`, completed successfully on 2026-09-17 UTC.

The original submission copied the proof project from the pinned Git objects.
The current documentation revision leaves Lean source, dependency pins and
verification scripts unchanged; the exact checked proof commit is listed above.

## Observed results

- `lake build --wfail`: success, 1,895 jobs.
- Bundled `leanchecker JSP000530`: success.
- Six named theorem axiom audits: only `propext`, `Classical.choice`, and
  `Quot.sound` occurred. No sorry, native-evaluation, or compiler-trust axiom
  was permitted by the audit.
- All nine dependency checkout revisions matched the lock file.
- The false-arithmetic negative control was rejected.
- The two final theorem dependency closures were exported to pinned NaNoda,
  with the same three-axiom allowlist and hard rejection of other axioms.
  It reported: `Checked 13905 declarations with no errors`.
- The dependency manifest was unchanged before and after the checks.

The compact `evidence/ci-excerpt.log` contains selected timestamped lines
from the actual job log; it is an excerpt, not the complete log.

Lake emitted a dependency-URL spelling warning because `lakefile.lean`
uses the `.git` suffix and the locked manifest URL omits it. Both identify
the same repository. The immutable revision checks and unchanged-manifest
checks passed. The Lean source itself compiled with warnings treated as
errors. The workflow also emitted GitHub's action-runtime deprecation notices.

## Full downloadable evidence

- Artifact: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169007348/artifacts/10476491626
- Artifact ID: `10476491626`
- Size: 9,175,963 bytes
- ZIP SHA-256: `bcd0c292377b0c3f8beff209c4f0c2b97c8603e1c807906220e3c6acaadb523b`
- Scheduled expiration: 2026-12-16 01:02:55 UTC.

The artifact includes the tested source archive, compiler/build logs, kernel
replay log, axiom output, negative control, independent-checker output,
printed statements, compressed proof export and checksums. Source and compact
evidence are committed; the artifact has finite retention and is not claimed
as permanent independent archival.

## Historical submission checks and current scope limit

The official repository's 22 unit tests and its validate, links, build,
check and history commands passed locally against base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. The local test transcript and
preflight receipt are in `evidence/`. Only this new submission directory
is added; no catalog flags, candidate records, awards, schemas, validators,
tests or recipient profiles are changed.

These are contributor-run checks, not organizer approval or independent
human review. Dependency caches and network access were used. No offline
full-library rebuild, official minimum-safe-version approval, new
mathematical discovery, global priority, or payment entitlement is claimed.
Review of statement fidelity, attribution, overlap, intake placement and
formalization-contribution eligibility remains with the maintainers.

## Unresolved full-scope requirement

The passing run checks the no-four-concyclic counterexample family. It does not check a solution with an additional no-three-collinear hypothesis. The current complete-only submission rule therefore cannot be certified from this run alone. See the current README for the precise remaining scope issue. No new complete-solution or eligibility status is asserted by this documentation update.
