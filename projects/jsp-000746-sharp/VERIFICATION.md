# Verification record

## Executed proof revision

The new integer endpoint and pinned Lean 4.34 project have passed local source compilation with warnings treated as errors, all three bundled-kernel replays, the exact integer theorem-type check, all eight target axiom audits, all nine dependency revision checks and the invalid-arithmetic negative control. Audited theorem closures contain only `propext`, `Classical.choice` and `Quot.sound`.

Modules: `Erdos895`, `JSP000746Sharp`, `JSP000746`.

The same checks passed in [GitHub Actions run 35278219789](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35278219789), executed at proof commit `4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a` on branch `jsp-000746-sharp-kz`. This is the selected proof version. The old Lean 4.33 run does not certify this version. The committed source checksum list binds the project inputs to the checked version.

## Reproduction and limits

Run `bash scripts/verify.sh` after bootstrap and dependency-cache setup. It compiles every source module, replays all three modules through Lean's bundled checker, checks the exact integer theorem and eight axiom closures, checks dependency revisions and requires false arithmetic to be rejected.

`check_built.py` alone checks already compiled modules; use `verify.sh` for the full compilation and checking sequence. Local logs are generated under `evidence/generated/`. The public workflow archives the logs, input hashes, version pins and executed repository commit.

This is contributor-run verification using downloaded dependency caches and Lean's own kernel replay. The historical Python witness and LRAT checks are separate finite checks, not a separately implemented general Lean kernel. These results do not constitute independent human statement review, a full offline Mathlib rebuild or organizer acceptance.
