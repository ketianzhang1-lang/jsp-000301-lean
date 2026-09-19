# JSP-000897: additional verified formalization contribution

Prepared by `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance, on 2026-09-19. This supplements existing [catalog PR #439](https://github.com/TheJustinSunPrize/awards/pull/439) and [award claim #1573](https://github.com/TheJustinSunPrize/awards/issues/1573).

## Scope and attribution

Our seven new theorems add quantitative stability when the selected vertex need not have maximum degree. Write n for the graph order, Delta for its maximum degree, d for the chosen vertex degree, s for a certified edge surplus and delta for a bound on Delta-d.

For every r >= 3, if `ex(n,K_r)+s <= e(G)` and `Delta <= d+delta`, the main new theorem proves

```text
ex(d,K_(r-1)) + s <= e(G[N(v)]) + delta*(n-d).
```

`surplus_loss_bound` gives the corresponding inequality between natural surplus counts. `strict_link_with_degree_deficit` proves a strict neighbourhood threshold whenever `delta*(n-d) < s`. The zero-deficit specialization `surplus_at_every_maximum_from_three` retains all surplus for every maximum-degree vertex and now includes r=3.

`complete_with_stability` keeps the original full endpoint for r>=4 and n>=2: an actual maximum-degree vertex has degree at least n/2 and retains the exact surplus. It adds the quantified stability result for every approximately maximum-degree vertex. The extension does not assert that the linear degree conclusion was proved for r=3, nor that the penalty is optimal.

`edge_bound_by_maxDegree` is an explicitly attributed adaptation of the existing edge-charging proof, retaining Delta instead of replacing it by d. `cliqueExtremal_split_from_three` adapts the credited splitting interface with its sufficient r>=3 hypothesis. The source preserves credit to Codex/GPT-5.6 Sol for the prior development and Bollobás, Thomason and Bondy for the underlying mathematics. We claim these specified formal extensions and their integration, not independent authorship of the reused arguments, new mathematical discovery or global priority.

## Immutable complete-package source

- Repository: `https://github.com/ketianzhang1-lang/jsp-000301-lean`.
- Branch: `jsp-000897-degree-stability-20260919`.
- Verified supplement commit: `4d15dc035f56658776c01729216f99b776a5ad35`.
- New proof module: [JSP000897Stability.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4d15dc035f56658776c01729216f99b776a5ad35/projects/jsp-000897/JSP000897Stability.lean).
- Original complete proof retained from `914c6fa28200985d6409b5b34588b9f5c4a87d00`. The new verifier compares every original Lean file, toolchain and dependency manifest against that selected version before building, then rechecks their hashes after execution.

The source commit contains the original full submission, dependencies and verification scripts together with the new supplement. It is not a standalone partial replacement for the complete proof. The linked documentation revision adds this review note and receipt; it changes no proof or checking input.

## Executed verification

[Public run 35415283467](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35415283467) succeeded at the exact supplement commit above. The original full build, original kernel replay and original axiom checks passed, followed by warning-as-error compilation and kernel replay of the new module. The combined audit checks **15 original and new targets**. A false-arithmetic proof after importing the new module was rejected for the expected reason.

Independent NaNoda checked **11,276 declarations with no errors** from those combined target closures. Its allowlist is exactly `propext`, `Classical.choice` and `Quot.sound`, with `unpermitted_axiom_hard_error=true`. The checker script also requires nonempty printed statements. The pinned exporter and checker are built from their recorded revisions.

[SUPPLEMENT_RECEIPT.json](SUPPLEMENT_RECEIPT.json) identifies the exact run, job, source and GitHub-reported artifact metadata. The artifact digest is service-reported rather than a claim of locally rehashing the ZIP. The workflow artifact contains the tested source, proof export, configuration and logs; it has finite retention.

Reproduce from `projects/jsp-000897` at the verified source commit with the committed Lean 4.34 toolchain and dependency manifest:

```bash
lake exe cache get
python3 scripts/verify_supplement.py
bash scripts/verify_supplement_nanoda.sh
```

The scripts require Git, Python, Lean/Lake, Rust/Cargo and network access. Nine dependency revisions remain locked. Cached Mathlib objects are used; this is not a fresh source rebuild of every dependency or an official offline verification. Contributor-operated machine checks do not establish independent human review, eligibility, acceptance or payment.
