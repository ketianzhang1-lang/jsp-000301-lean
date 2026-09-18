# Executed verification of the complete JSP-000393 development

We executed the integrated proof checks on 2026-09-17 using Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435` with nine locked package
revisions. The following checks passed:

| Check | Actual result |
| --- | --- |
| Upstream sources | All 22 original/ported input hashes matched the immutable register. |
| Compilation | 25 modules passed with `-DwarningAsError=true`, `-j1`, and `-M10000`. |
| Target axiom audit | All 13 declaration dependency closures used only `propext`, `Classical.choice` and `Quot.sound`. |
| Kernel replay | All 22 upstream proof modules and both our proof modules passed. |
| Dependency revisions | All nine Git revisions matched the committed manifest. |
| False-arithmetic control | The invalid proof of `(1 : Nat) = 0` was rejected. |
| Source preservation | `JSP000393.lean` is byte-identical to its original verified source at `a337720331a34599114a9d4669d6518d5e608f6f`. |

The [execution record](verification/local-verification.json) lists all compiled
modules and exact source SHA-256 values. The recorded `preparation_head` is the
base revision of the local worktree; it is not presented as the later public
commit containing the new files. The source hashes identify the actual tested
inputs. `SOURCE_SHA256SUMS` identifies the proof, dependency, workflow and verifier
inputs committed with this revision.

Retained transcripts:

- [Axiom reports](verification/axioms.log)
- [22-module upstream replay](verification/kernel-upstream.log)
- [Our original construction replay](verification/kernel-construction.log)
- [Our integration replay](verification/kernel-integration.log)
- [Rejected invalid proof](verification/negative-control.log)

## Reproduction and limits

From the selected public proof commit on `jsp-000393-sparse-squares`, run:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
python3 scripts/verify_complete.py
```

The verifier enforces `LEAN_NUM_THREADS=1`. An initial replay using unrestricted
parallelism exceeded the local 20 GiB memory limit and was terminated; it did
not report a theorem error. After the successful 25-module build, the replay
phase was resumed with one Lean worker and all stages passed. The source hashes
were checked after completion. The workflow uses the same single-worker setting
and provides additional swap space on the hosted runner.

Network access and cached Mathlib dependencies were used. The bundled
`leanchecker` uses Lean's own kernel and imports the pinned Mathlib environment;
it is not an independent checker implementation or a fresh replay of every
Mathlib declaration. The initial checks above did not include NaNoda. The successful independent
NaNoda replay of the complete target closures is recorded below. These are contributor-run checks, not independent human
certification or organizer approval.

The public workflow records the exact source commit and uploads full execution
logs with 90-day retention. A workflow file or queued run alone is not a claim
of a completed public run; consult the exact run status linked in PR #368.


## Independent NaNoda verification — 2026-09-18

We independently checked all 13 audited target dependency closures with NaNoda in [run 35302255801](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302255801), at commit `0e86d155839b409faa075233a1b62e32f2b7b1e3`. The checker reported **34,637 declarations with no errors**, and statement printing also succeeded. The same run passed the full source compilation, Lean kernel replay, original axiom audits and false-arithmetic negative control.

The export includes `JSP000393Complete.jsp_000393`, the complete upstream `Erdos485.erdos_485` theorem, our construction, and all other targets in `AuditComplete.lean`. Every target is exported with its full dependency closure. Only `propext`, `Classical.choice` and `Quot.sound` are permitted, with `unpermitted_axiom_hard_error: true`; no `sorryAx`, compiler-trust axiom or custom unproved axiom is allowed.

[The source comparison](https://github.com/ketianzhang1-lang/jsp-000301-lean/compare/17e406594d644b40c9a742e843cd6d89f319c872...0e86d155839b409faa075233a1b62e32f2b7b1e3) confirms that the Lean proof files, upstream source pins and dependency manifest are unchanged from the selected proof commit `17e406594d644b40c9a742e843cd6d89f319c872`. We added checker integration and evidence collection; no mathematical proof repair was needed.

To reproduce the complete check, check out `0e86d155839b409faa075233a1b62e32f2b7b1e3` and run at the repository root:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
python3 scripts/verify_complete.py
bash scripts/verify_nanoda.sh
```

The checker script pins lean4export to `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, builds them from source and requires error-free checking and nonempty statement output. Git, Python 3, Lean/Lake and Rust/Cargo with network access are required. The public CI performs the whole sequence.

[The machine-readable CI receipt](verification/nanoda-ci.json) records the exact run, source comparison, checked targets and artifact digest. The workflow artifact includes the compressed exported proof, checker configuration, printed statements and logs under `nanoda/` and is retained for 90 days. NaNoda is a separately implemented checker; this contributor-run verification is not independent human review or organizer approval.
