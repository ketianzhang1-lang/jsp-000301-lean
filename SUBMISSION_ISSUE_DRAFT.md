# Recipient recommendation — prepared, not submitted

Status: an integration attempt to create an official issue returned HTTP 403 on September 16, 2026. No official issue number or PR receipt exists from that attempt. The text below is ready for the official recipient form, but does not replace a required formal PR.

Suggested issue title:

`[Recipient] JSP-000301 — Lean formalization with pinned dependencies, NaNoda and axiom-audit evidence`

---

### Related problem or entry

[JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301): If two consecutive positive integers are powerful, must at least one be a perfect square?

### Recipient placeholder or confirmed public ID

`RECIPIENT-JSP-000301-KZ-A`, an issue-local placeholder distinguishing this recommendation from earlier filings. Submitting public account and repository owner: `ketianzhang1-lang`. Final recipient confirmation and contribution attribution remain pending.

### Contributions and evidence

The catalog already records `12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`, with both numbers strictly between `110^2` and `111^2`. The mathematics is not claimed as new work. This project contributes its Lean formalization and reproducible verification evidence only.

- Verified proof and locked-dependency commit: `e1a17b0d6728b9d4929d1d4abd3721a27377369a`.
- Source: https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e1a17b0d6728b9d4929d1d4abd3721a27377369a/JSP000301.lean
- Manifest: https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e1a17b0d6728b9d4929d1d4abd3721a27377369a/lake-manifest.json
- Passing run #13: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133
- Earlier passing run #12: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35130895580
- Lean v4.34.0; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

`Powerful n` is `∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n`. `PerfectSquare n` is `∃ m : ℕ, m ^ 2 = n`. The two main results are:

```lean
JSP000301.jsp_000301_counterexample :
  ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
    ¬ PerfectSquare n ∧ ¬ PerfectSquare (n + 1)

JSP000301.jsp_000301_disproved :
  ¬ (∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
    PerfectSquare n ∨ PerfectSquare (n + 1))
```

Here the predicates in these displayed types are qualified by the namespace `JSP000301`. Positivity is explicit, and the statement covers only the catalog's yes/no question, not Erdős #365's separate counting question or three consecutive powerful integers.

Observed verification in run #13: `lake build --wfail` succeeded, bundled leanchecker succeeded, NaNoda checked 188,335 declarations with no typechecker errors, and separate axiom-audit checked 9 project declarations against `[propext, Classical.choice, Quot.sound]`. NaNoda also reports one pretty-printer error, `Unable to print axioms`; the separate project axiom audit passes. The source contains no `sorry`, `admit`, `native_decide` or added axioms.

The pinned workflow records the exporter/checker revisions. NaNoda's whole-environment allowlist additionally contains `Lean.trustCompiler`; the separate project audit uses only the three axioms above. The workflow changes upstream tool checkout revisions, not checker semantics.

Reproduce:

```sh
git clone https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout --detach e1a17b0d6728b9d4929d1d4abd3721a27377369a
lake exe cache get
lake build --wfail
lake env leanchecker JSP000301
```

The workflow at that commit specifies the additional external checks. Preserve the committed manifest; do not run `lake update` for this reproduction.

These are contributor-controlled, network-enabled GitHub-hosted runs using upstream precompiled Mathlib files. They do not establish official offline verification, minimum-safe-version approval or independent human statement review. Lean's build and bundled leanchecker share an implementation; NaNoda is the separate implementation. No externally peer-verified registration exemption is claimed.

AI assistance: OpenAI ChatGPT assisted with source, documentation and CI repairs under the submitter's direction. The submitting account operates the project. The maintainers should determine the appropriate formalization/operator attribution.

### Confirmation status

Pending. No official recipient confirmation or KYC has been completed. No private identity documents, contact details or payment information are posted here. Required private confirmations should use the designated official channel.

### Attribution questions and conflicts

This is a self-recommendation of the submitting account's AI-assisted project, not an independent review. Earlier filings include #25, #62, #64, #82, #94, #109, #146 and #156. No first-formalization priority is claimed and no claim is made that more checker evidence supersedes an earlier valid formalization.

Please advise whether this later submission remains eligible for formalization contribution recognition, including any applicable same-window provisions, and the required PR/record route under Selection Rules §§4.1 and 6. No award tier or payment amount is asserted. This issue is a review request, not evidence that formal entry, award adjudication or payment approval has occurred. Additional professional conflicts have not been independently confirmed for this record.
