# Verification receipt: JSP-000399, n = 27, k = 3

Status: **passed automated proof checks**, 2026-09-17 UTC. This receipt is
contributor-provided evidence, not an organizer review or an award decision.

## Exact tested inputs

- [Proof commit 688bef3f9616373391bd50739a34e71c072bbaad](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/688bef3f9616373391bd50739a34e71c072bbaad/projects/jsp-000399-27).
- [Passing run 35168554058 / job 105035022466](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168554058/job/105035022466), completed at 01:02:33 UTC.
- Lean 4.34.0, compiler commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`; all nine dependency revisions matched the committed manifest.
- The current proof files, challenge, audit, package configuration, lockfile, and verification scripts were compared byte-for-byte with the source archive from the passing run. Later documentation and receipt additions do not alter these inputs. Their hashes are in [PROOF_INPUT_SHA256SUMS](evidence/PROOF_INPUT_SHA256SUMS).

## Results

| Check | Result |
| --- | --- |
| `lake build --wfail` | Passed, 969 build jobs |
| `leanchecker Adapter` and `leanchecker JSP000399Triple` | Both exited successfully |
| Six target `#print axioms` audits | Only `propext`, `Classical.choice`, `Quot.sound` |
| `Challenge.lean` | Passed; independently restates the exact finite-set and multiset definitions |
| Manifest and dependency revision checks | Passed |
| False arithmetic negative control | Correctly rejected `1 = 0` |
| Independent Python enumeration | Both sets have 27 distinct elements; all 2,925 triple sums per set agree with multiplicity; changed input rejected |
| NaNoda dependency-closure check | **8,129 declarations checked, no errors** |

The proof uses `decide +kernel`; it contains no `sorry`, `admit`, custom axioms,
`native_decide`, or unsafe proof replacement. The final complex counterexample
and nonuniqueness theorem have no extra hypotheses. The finite certificate
proves both support bounds and every multiplicity in the interval [-54,54].

NaNoda was pinned to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, and
lean4export to `6cea97789dc088ea47fcea15692db85685aedac5`. The export contains
the two endpoint theorems and their complete dependency closure. Its configuration
permits only the three standard axioms above and treats other axioms as errors.
See [configuration](evidence/nanoda-config.json), [checked statements](evidence/nanoda-statements.txt),
[axiom audit](evidence/axioms.log), [NaNoda result](evidence/nanoda.log), and
[full CI job log](evidence/github-job.log). Empty kernel/challenge logs record
successful silent commands; the fail-fast script and successful job establish
their exit status.

## Artifact and retention

[Artifact 10476426358](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168554058/artifacts/10476426358)
contains the source archive, checker export, configuration, and logs.
The ZIP was downloaded and its hash was checked before this receipt was written.

| File | SHA-256 |
| --- | --- |
| Artifact ZIP, 5,298,333 bytes | `a824f500d80c2da8ad6a815b6dd082ff29aa1b78621f443a15fff56652c8e20c` |
| `source.tar.gz` | `a5bc65ac139f560dc1e8c1f2d8c1222ee43d6f7e1a7d8a5f2cf85380549f5b1b` |
| `export.ndjson.gz` | `548e9a0978cd7fac49f42d998e1909fddf4383433a7d9a8d885425e1bfa3335d` |

GitHub lists artifact expiry as **2026-12-16 00:56:14 UTC**. Text receipts are
committed alongside the source; the binary archives remain in the expiring CI
artifact and can be regenerated with the pinned scripts. No permanent archive
or third-party archival attestation is claimed.

## Scope and limits

This verifies the known exceptional **(n,k) = (27,3)** nonuniqueness component
of JSP-000399 / Erdős Problem 494. It does not classify all cardinalities and
subset sizes. The original-definition comparison is an independently stated
interface; this project does not import the complete Formal Conjectures repository.
The inspected original source is pinned in README.md.

These checks ran on the contributor's GitHub Actions runner using cached
dependencies and network access. No independent human review, organizer
acceptance, global priority, offline dependency rebuild, prize tier, or payment
entitlement is asserted. Repository record validation is separate from proof
verification and from the organizer's decision.
