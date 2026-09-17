# Verification evidence

All reported checks below passed on 2026-09-17 UTC. These are applicant-run
checks, not an organizer decision or independent human certification.

## Fixed proof source and environment

- Proof commit: `e3191a77503c145dde16a2b4e4a9489a92947812`.
- Proof SHA-256: `e41cf87887310cfbc9a1c83e70e090ddc790e35e6c504b16599b39360180060d` (`JSP000140.lean`).
- Lean `v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Every dependency revision is locked in `lake-manifest.json` and checked.
- [Dedicated cloud run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178843250),
  job `105066430084`, conclusion `success`.

## Completed mathematical checks

| Check | Result |
| --- | --- |
| Local Lean frontend at trust level 0 | Passed, no errors or warnings |
| Standard cloud `lake build --wfail` | Passed for proof and Audit modules |
| `leanchecker JSP000140` and `leanchecker Audit` | Both passed |
| Ten target axiom audits | Exactly propext, Classical.choice, Quot.sound |
| Locked dependency revision comparisons | Passed |
| Invalid arithmetic proof negative control | Rejected as required |
| Separate NaNoda checker | 6,554 declarations checked with no errors |

The NaNoda targets are `fork_packing`, `strict_lower_bound`,
`integer_lower_bound`, and `lower_bound_from_vertex_sets`, including their full
exported dependency closures. Its only permitted axioms are propext,
Classical.choice and Quot.sound, with hard errors on other axioms.
Exporter revision: `6cea97789dc088ea47fcea15692db85685aedac5`.
Checker revision: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

The full decoded cloud job transcript is preserved in
`evidence/cloud-workflow.log`; the local audit is in `evidence/local-axioms.log`.
The latter was run by appending the audit commands to the proof source through
a local Lake frontend runner. The standard imported-module build was then
verified by the dedicated cloud workflow.

## Archived workflow evidence

GitHub reports the following artifact; the receipt is preserved as
`evidence/cloud-artifact.json`:

- Name: `jsp-000140-evidence`; ID: `10479915118`.
- Size: `4572004` bytes.
- ZIP digest: `sha256:3854184ba587692eeb85b38e73196d0605aa15b312719aa5518679c257429eb0`.
- Retention expiration: `2026-12-16T03:37:12Z`.

The artifact contains build, axiom, kernel and negative-control logs, exported
proof dependencies, NaNoda configuration/output and an archive of tested source.
The size and ZIP digest above are the GitHub API receipt; no local download or
independent recomputation of that ZIP digest is claimed. The source and decoded
job transcript are separately committed so the review does not rely solely on
the artifact's finite retention.

## Submission checks and limits

In an isolated copy of organizer main `f4e7173d89dfe91022a185427d63452c8ffbf6ae`,
validate, links, build and check passed, as did all 22 repository unit tests.
The log is `evidence/repository-preflight.log`. This validates repository
packaging, not the mathematics. No existing record or generated data changes.

Upstream Mathlib caches and network access were used. No clean rebuild of all
Mathlib source, designated organizer verifier, independent human statement
review, or organizer-approved compiler-version decision is claimed. Existing
public formalization is disclosed in README.md. This package covers only the
lower bound; the full asymptotic upper bound is outside scope.
