# Verification of the complete JSP-000140 package

The full package passed [GitHub run 35347120839](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35347120839) on 2026-09-18.
The tested proof commit is **`724a733a2b498d7b3b956e66b76d7334cc906eaf`**, on branch
`jsp-000140-coloring-kz`. This is an executed result, not merely a workflow recipe.

| Check | Executed result |
| --- | --- |
| Full source closure | All 24 proof/audit modules compiled; Lean warnings treated as errors |
| Source and dependency pins | 20 imported source modules hash-checked; all nine dependency revisions checked |
| Axiom audit | 46 selected theorem closures; only `propext`, `Classical.choice`, `Quot.sound` permitted |
| Kernel replay | `ErdosProblems`, `JSP000140`, `JSP000140Bridge`, `JSP000140Complete` passed |
| Negative control | The false statement `(1 : Nat) = 0` was rejected |
| Independent NaNoda | **56,007 declarations checked with no errors** |

The 46 selected roots comprise all 44 public lemmas/theorems in our three
modules and both complete imported asymptotic endpoints. The exported dependency
closures passed NaNoda with `unpermitted_axiom_hard_error=true` and the same
three-axiom allowlist. The checked closures do not rely on `sorryAx` or extra
axioms standing in for missing proofs.

Lean is fixed to 4.34.0 and Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`.
The exporter is fixed to `6cea97789dc088ea47fcea15692db85685aedac5`;
NaNoda is fixed to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
README.md gives fresh-checkout reproduction commands.

## Durable evidence

- [Complete hosted job log](verification/ci-35347120839.log)
- [Machine-readable receipt](verification/ci-receipt.json)
- [Workflow artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35347120839/artifacts/10549376826), including detailed build,
  axiom, kernel, negative-control and NaNoda logs, source hashes, printed
  statements and the exported proof closure.
- GitHub-reported artifact ZIP digest: `sha256:7432ef2d7099aab2264dc4d31eb25e7d2ebec54f5c58506cc9c3a2039dc391c3`.
  This value is reported by the artifact API and upload log; the ZIP was not
  independently downloaded and rehashed.
- Archived job-log SHA-256: `6fb4b7f449796fd0eba21311685229294695cf3ab7cf09312a46f9582e327bfc`.

The original lower-bound source remains byte-identical to its earlier version,
with SHA-256 `e41cf87887310cfbc9a1c83e70e090ddc790e35e6c504b16599b39360180060d`.
Earlier lower-bound-only evidence is historical and does not certify the
complete endpoint.

These are contributor-run machine checks. Statement fidelity, contribution
eligibility, priority and prize decisions remain subject to maintainer review.
The reused full asymptotic proof is disclosed in PROVENANCE.md.
