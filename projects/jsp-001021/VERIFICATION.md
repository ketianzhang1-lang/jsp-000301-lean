# Verification record

The complete Lean dependency chain passed source compilation, four bundled-kernel replays, eleven strict target axiom audits, exact-statement checks, nine dependency revision checks and a false-arithmetic negative control in [run 35279395960](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35279395960), at proof commit `7642a7f5eb190da6319b6ae7f11c829d7737e2dd`. The earlier Python output is supplementary evidence and is not offered as Lean verification.

`bash scripts/verify.sh` compiles the two pinned upstream modules, `FiniteChecks.lean` and `JSP001021.lean`, replays all four modules, checks the exact fifteen-vertex and universal-negation statements, audits eleven theorem closures, checks actual dependency revisions and rejects an invalid arithmetic statement.

The workflow preserves logs and source hashes under `evidence/generated/` and archives the executed repository commit. Contributor-run builds use network access and Mathlib caches; they are not independent human certification or a fully offline dependency rebuild. The local certificates establish the exclusions stated in their theorem, while the full main theorem uses the attributed fourteen-vertex proof.


## Independent NaNoda verification — 2026-09-18

We independently checked all 11 audited target dependency closures with NaNoda in [run 35302257717](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302257717), at commit `3ebcc72d98b50f59ff456feb5963f85815b2d09c`. The checker reported **6,715 declarations with no errors**, and statement printing also succeeded. The same run passed source compilation, four Lean kernel replays, the original eleven axiom audits, exact-statement checks, dependency revision checks and the false-arithmetic negative control.

The export includes the complete universal negation `JSP001021.jsp_001021`, our fifteen-vertex result, the upstream fourteen-vertex theorems and all other targets in `Audit.lean`. Every target is exported with its full dependency closure. Only `propext`, `Classical.choice` and `Quot.sound` are permitted, with `unpermitted_axiom_hard_error: true`; no `sorryAx`, compiler-trust axiom or custom unproved axiom is allowed.

[The source comparison](https://github.com/ketianzhang1-lang/jsp-000301-lean/compare/7642a7f5eb190da6319b6ae7f11c829d7737e2dd...3ebcc72d98b50f59ff456feb5963f85815b2d09c) confirms that the Lean proof files, upstream source pins and dependency manifest are unchanged from the selected proof commit `7642a7f5eb190da6319b6ae7f11c829d7737e2dd`. We added checker integration and evidence collection; no mathematical proof repair was needed.

To reproduce this additional check, check out `3ebcc72d98b50f59ff456feb5963f85815b2d09c`, enter `projects/jsp-001021`, run the documented bootstrap, dependency-cache setup and full `bash scripts/verify.sh` sequence, then run:

```bash
bash scripts/verify_nanoda.sh
```

The checker script pins lean4export to `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, builds them from source and requires error-free checking and nonempty statement output. Git, Python 3, Lean/Lake and Rust/Cargo with network access are required. The public CI performs the whole sequence. The finite certificates require substantial computation and memory, so the workflow provides swap space.

[The machine-readable CI receipt](verification/nanoda-ci.json) records the exact run, source comparison, checked targets and artifact digest. The workflow artifact includes the compressed exported proof, checker configuration, printed statements and logs under `nanoda/` and is retained for 90 days. NaNoda is a separately implemented checker; this contributor-run verification is not independent human review or organizer approval.
