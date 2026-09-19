# JSP-000465: additional verified formalization contribution

Prepared by `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance, on 2026-09-19. This supplements existing [catalog PR #442](https://github.com/TheJustinSunPrize/awards/pull/442) and [award claim #1572](https://github.com/TheJustinSunPrize/awards/issues/1572).

## Scope and attribution

Our five new theorems make the existing simultaneous separation usable with relative errors and changing comparison members:

- `eventually_member_positive` proves that all member extremal numbers are positive beyond one common threshold. The ratio result therefore does not depend on assigning a value to division by zero.
- `uniform_ratio_small` proves that, for every real epsilon > 0, the ratio ex(n,F)/ex(n,H) is below epsilon for all sufficiently large n and **every H in the same fixed finite family**.
- `adaptive_ratio_tendsto` allows an arbitrary choice H(n), with membership in the family required only eventually, and proves that its ratio tends to zero. There is no monotonicity or constant-choice hypothesis.
- `no_adaptive_comparison` excludes every positive constant-factor upper comparison even when H depends on n.
- `adaptive_compactness_counterexample` states the resulting negative adaptive formulation while retaining a nonempty finite family whose members are connected, bipartite and cyclic.

The complete original endpoint remains in the unchanged `JSP000465.lean`. The new file imports that endpoint and its estimates. It supplies formal consequences and a stronger interface; it does not claim a new quantitative construction, a new mathematical counterexample or global priority. The substantive construction and lower/little-o estimates retain their OpenAI/Astra attribution in the imported Erdős 180 development. Our earlier simultaneous-separation proof is used directly in the new ratio and adaptive-selection results.

## Immutable complete-package source

- Repository: `https://github.com/ketianzhang1-lang/jsp-000301-lean`.
- Branch: `jsp-000465-uniform-ratios-20260919`.
- Verified supplement commit: `78dbc684a1ce3d392b150d98bdc5b94a9269f3e3`.
- New proof module: [JSP000465Uniform.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/78dbc684a1ce3d392b150d98bdc5b94a9269f3e3/projects/jsp-000465/JSP000465Uniform.lean).
- Original complete proof retained from `6a793b157c1afdf29f3e6bbbf3cf514535d1dfca`. The new verifier compares every original Lean file, toolchain and dependency manifest against that selected version before building, then rechecks their hashes after execution.

The source commit contains the original full submission, dependencies and verification scripts together with the new supplement. It is not a standalone partial replacement for the complete proof. The linked documentation revision adds this review note and receipt; it changes no proof or checking input.

## Executed verification

[Public run 35415279784](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35415279784) succeeded at the exact supplement commit above. The original full build, original kernel replay and original axiom checks passed, followed by warning-as-error compilation and kernel replay of the new module. The combined audit checks **12 original and new targets**. A false-arithmetic proof after importing the new module was rejected for the expected reason.

Independent NaNoda checked **42,577 declarations with no errors** from those combined target closures. Its allowlist is exactly `propext`, `Classical.choice` and `Quot.sound`, with `unpermitted_axiom_hard_error=true`. The checker script also requires nonempty printed statements. The pinned exporter and checker are built from their recorded revisions.

[SUPPLEMENT_RECEIPT.json](SUPPLEMENT_RECEIPT.json) identifies the exact run, job, source and GitHub-reported artifact metadata. The artifact digest is service-reported rather than a claim of locally rehashing the ZIP. The workflow artifact contains the tested source, proof export, configuration and logs; it has finite retention.

Reproduce from `projects/jsp-000465` at the verified source commit with the committed Lean 4.34 toolchain and dependency manifest:

```bash
lake exe cache get
python3 scripts/verify_supplement.py
bash scripts/verify_supplement_nanoda.sh
```

The scripts require Git, Python, Lean/Lake, Rust/Cargo and network access. Nine dependency revisions remain locked. Cached Mathlib objects are used; this is not a fresh source rebuild of every dependency or an official offline verification. Contributor-operated machine checks do not establish independent human review, eligibility, acceptance or payment.
