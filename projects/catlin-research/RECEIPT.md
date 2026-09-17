# Verification receipt — sharp Catlin classification

Checked on 2026-09-17 UTC. This is contributor-provided reproduction evidence,
not independent human review or an organizer decision.

## Immutable tested source

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Tested commit: `019467ead20f2d6b87e672a1dfef7d5b8886febf`
- Project: `projects/catlin-research`
- Main endpoint: `CatlinComplete.sharp_catlin_counterexample`
- New source: [Sharp.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/019467ead20f2d6b87e672a1dfef7d5b8886febf/projects/catlin-research/Sharp.lean)
- The endpoint proves chromatic number 8 and, for every natural r, existence
  of a K_r subdivision if and only if r <= 7 in the explicit 15-vertex C5[K3].

## Executed checks

[GitHub Actions run 35176307046](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176307046)
completed with conclusion `success`; its head SHA matches the tested commit above.
Job ID: 105058663592. The run was last updated at 2026-09-17T03:00:24Z.

| Check | Observed result |
| --- | --- |
| Pinned Lean 4.34.0 and manifest dependencies | Installed successfully; actual Git revisions matched the manifest |
| Clean Lake build with warnings treated as errors | Passed |
| Bundled leanchecker replay of all seven proof modules | Passed |
| Twelve named theorem axiom audits | Passed; only propext, Classical.choice, Quot.sound permitted |
| False arithmetic control (1 = 0) | Rejected as required |
| Separate NaNoda implementation | Checked 7,621 declarations with no errors |
| Tested source and evidence archive | Uploaded successfully |

The exact reproduction scripts and pinned checker revisions are in the tested
source. Mathlib revision: `5ed2965256430c3649e86755f9576b54eca72435`.
The three new audited endpoints are `contains_K7_subdivision`,
`containsCliqueSubdivision_antitone`, and `sharp_catlin_counterexample`,
all in namespace `CatlinComplete`.

## Artifact identity and retention

- [Artifact 10479205805](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176307046/artifacts/10479205805)
- Name: `catlin-sharp-evidence`
- Size: 4940999 bytes
- SHA-256: `f11ea3fb5b03dda318c0d7dbded5060b3d7bbdf725896bf3fbd9b4f9321d3878`
- Created: 2026-09-17T03:00:20Z
- Reported expiry: 2026-12-16T02:56:40Z
- Not expired when queried. GitHub Actions artifacts have finite retention.

The archive includes source, manifest, build/replay/audit logs, the negative
control, exported declarations, NaNoda configuration, checked statements and hashes.
The Git commit preserves source after artifact expiry, but availability of the
artifact or logs after that date is not promised.

## Repair and mathematical contribution

The earlier run 35175254966 failed because Lake did not register the Profile
and other auxiliary modules. Commit 9ce0e526bb4f81ce9d42436b851be10b376236a0
repaired module registration; run 35175957870 then passed, including NaNoda's
7,495-declaration check. The sharp supplement adds an explicit K7 subdivision
and a restriction theorem to obtain the exact threshold. No proof assumption,
axiom policy or verification gate was weakened.

See [SHARP_PROOF.md](SHARP_PROOF.md) for the new construction and
[PROVENANCE.md](PROVENANCE.md) for the existing code lineage. Classical mathematical
credit belongs to Catlin; formalization was prepared with OpenAI ChatGPT assistance.

## Prize scope

This is the finite Catlin counterexample and its exact subdivision number.
It does not establish the full uniform asymptotic inequality of JSP-000585 /
Erdos 717 for arbitrary graphs. Please assess this scoped formalization separately;
no catalog eligibility change, first-formalization priority, official candidate
status, award, or payment entitlement is asserted.
