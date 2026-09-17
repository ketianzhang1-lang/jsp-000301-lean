# Verification receipt

These are contributor-run checks, including an independent checker
implementation. They are not independent human review or organizer approval.

## Pinned source and actual execution

- [Proof source 6a793b157c1afdf29f3e6bbbf3cf514535d1dfca](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/6a793b157c1afdf29f3e6bbbf3cf514535d1dfca/projects/jsp-000465).
- [Successful public run 35178564666](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178564666).
- [Successful job 105065585425](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178564666/job/105065585425).
- [Exact workflow](evidence/PROOF_WORKFLOW.yml).
- Checks completed 2026-09-17 UTC with Lean 4.34.0 and Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.

The 23 project files copied into the original submission matched the pinned proof
source byte-for-byte. Their historical SHA-256 hashes are in [historical source checksums](evidence/PROOF_SHA256SUMS). The uploaded Git tree
also matched the locally prepared tree.

| Check | Observed result |
| --- | --- |
| Build with warnings treated as errors | Success; 8,932 build jobs |
| Bundled Lean kernel replay | All eight local proof modules succeeded |
| Seven named axiom closures | Only `propext`, `Classical.choice`, `Quot.sound` |
| Actual dependency Git revisions | All matched the lockfile |
| Invalid arithmetic negative control | `1 = 0` rejected as required |
| NaNoda strict-allowlist verification | 42,570 declarations checked with no errors |
| Source and checker-export archiving | Success |

The seven audited roots are listed in [TARGETS.json](TARGETS.json),
including the substantive upstream quantitative counterexample, all new
problem-interface results, and the definition and attainment checks. No project
axiom, unfinished-proof axiom, or native-evaluation axiom is permitted.

NaNoda revision: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
Exporter revision: `6cea97789dc088ea47fcea15692db85685aedac5`.
All seven theorem closures were exported and replayed under the strict
three-axiom allowlist. The Ubuntu 24.04 run used network access and dependency
caches; no air-gapped full Mathlib source rebuild is claimed.

Compact public receipts: [log excerpt](evidence/public-log-excerpt.txt),
[run status](evidence/run-status.json), and
[artifact metadata](evidence/artifact-metadata.json).
The README at the immutable proof commit predates execution. The current README
records these completed results; proof files, dependency pins and scripts are unchanged.

## Failed preliminary run

[Run 35178387213](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178387213)
failed because the Lake library configuration declared only the terminal module
and omitted the six other upstream module roots. Commit
`6a793b157c1afdf29f3e6bbbf3cf514535d1dfca` declares all seven roots.
The proof files were unchanged by that build-configuration fix. The successful
run above rebuilt and checked the corrected package.

## External artifact and retention

[Artifact 10479855210](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178564666/artifacts/10479855210)
contains tested source, build and audit logs, negative-control output, the
compressed proof export, checker configuration, printed statements, dependency
lockfile, and checksums.

| Field | Service-reported value |
| --- | --- |
| Name | `jsp-000465-evidence` |
| ZIP bytes | `52724179` |
| ZIP SHA-256 | `cd7d191fe9d20f984acda5e884a6e513f36f3b4fc4dcf1675c602c398379a9fb` |
| Created | `2026-09-17T03:38:59Z` |
| Reported expiry | `2026-12-16T03:32:42Z` |

The upload log and API metadata agree on the ID, byte count, and ZIP digest.
The ZIP was not downloaded and rehashed locally; those are service-reported
values. The artifact has finite retention and is not an independent permanent
archive. The committed source, hashes, scripts, and compact receipts remain
available independently of that artifact's retention. Reviewers may preserve
the artifact or reproduce the scripts.

## Historical organizer-repository preflight (original submission)

Against base `f4e7173d89dfe91022a185427d63452c8ffbf6ae`, all 22 repository tests
passed, together with validate, links, build, check, and history. These are
local contributor-run repository checks. That historical change was confined to the original
submission directory; generated data and existing records are unchanged.
Structural checks do not decide mathematical attribution, contribution
eligibility, or payment.
