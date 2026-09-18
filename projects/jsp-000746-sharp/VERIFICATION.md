# Verification record

## Executed proof revision

The new integer endpoint and pinned Lean 4.34 project have passed local source compilation with warnings treated as errors, all three bundled-kernel replays, the exact integer theorem-type check, all eight target axiom audits, all nine dependency revision checks and the invalid-arithmetic negative control. Audited theorem closures contain only `propext`, `Classical.choice` and `Quot.sound`.

Modules: `Erdos895`, `JSP000746Sharp`, `JSP000746`.

The same checks passed in [GitHub Actions run 35278219789](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35278219789), executed at proof commit `4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a` on branch `jsp-000746-sharp-kz`. This is the selected proof version. The old Lean 4.33 run does not certify this version. The committed source checksum list binds the project inputs to the checked version.

## Reproduction and limits

Run `bash scripts/verify.sh` after bootstrap and dependency-cache setup. It compiles every source module, replays all three modules through Lean's bundled checker, checks the exact integer theorem and eight axiom closures, checks dependency revisions and requires false arithmetic to be rejected.

`check_built.py` alone checks already compiled modules; use `verify.sh` for the full compilation and checking sequence. Local logs are generated under `evidence/generated/`. The public workflow archives the logs, input hashes, version pins and executed repository commit.

This is contributor-run verification using downloaded dependency caches and Lean's own kernel replay. The historical Python witness and LRAT checks are separate finite checks, not a separately implemented general Lean kernel. These results do not constitute independent human statement review, a full offline Mathlib rebuild or organizer acceptance.


## Independent NaNoda verification

We independently checked all 8 audited target dependency closures with NaNoda in [run 35302256694](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302256694), at commit `d38c1169bbea335d1683589ba2bda3cf78c1b932`. The checker reported **5,363 declarations with no errors**, and statement printing also succeeded. The same run passed source compilation, Lean kernel replay, the original axiom audits and the negative control.

The allowlist contains only `propext`, `Classical.choice` and `Quot.sound`, with `unpermitted_axiom_hard_error: true`. The exported targets include `JSP000746.jsp_000746`, the finite sharp threshold, and the upstream upper-bound theorem. No `sorryAx`, compiler-trust axiom or custom unproved axiom is permitted.

[The source comparison](https://github.com/ketianzhang1-lang/jsp-000301-lean/compare/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a...d38c1169bbea335d1683589ba2bda3cf78c1b932) confirms that the Lean proof files, upstream source pins and dependency manifest are unchanged from the selected proof commit `4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a`. We added the checker integration and evidence collection; no mathematical proof repair was needed.

To reproduce this additional check, check out `d38c1169bbea335d1683589ba2bda3cf78c1b932`, enter `projects/jsp-000746-sharp`, run the bootstrap, dependency setup and full `bash scripts/verify.sh` sequence, then run:

```bash
bash scripts/verify_nanoda.sh
```

The script pins lean4export to `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, builds them from source, exports the full target closures, checks them with the strict allowlist and requires error-free checking and nonempty statement output. Git, Python 3, Lean/Lake and Rust/Cargo with network access are required. The public CI performs the whole sequence.

[The machine-readable CI receipt](verification/nanoda-ci.json) records the exact run, source comparison, checked targets and artifact digest. The run artifact includes the compressed exported proof, checker configuration, printed statements and logs under `nanoda/` and is retained for 90 days. NaNoda is a separately implemented checker; this contributor-run verification is not independent human review or organizer approval.
