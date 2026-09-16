# JSP-000301 — Lean 4 formalization

This project formalizes the **already-known** counterexample to the catalog question:
if two consecutive positive integers are powerful, must at least one be a square?
The witness is `12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`, neither a square.
No new mathematical discovery or first-formalization priority is claimed.

## Verified snapshot

- Proof and dependency-lock commit: `e1a17b0d6728b9d4929d1d4abd3721a27377369a`.
- [Passing run #13](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133), reproduced with the committed dependency manifest.
- [Passing run #12](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35130895580), before committing the generated manifest.
- Lean `v4.34.0`; Mathlib `v4.34.0` at `5ed2965256430c3649e86755f9576b54eca72435`.
- `lake build --wfail`, bundled `leanchecker`, NaNoda and project axiom-audit passed.
- NaNoda reported no typechecker errors and one pretty-printer error; details and limits are in [VERIFICATION.md](VERIFICATION.md).

This is contributor-generated verification evidence, **not official prize verification, an award, or payment approval**. Documentation added after the verified snapshot does not change which proof commit was checked.

## Reproduce the verified proof

With Git and the Lean/elan toolchain manager installed:

```sh
git clone https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout --detach e1a17b0d6728b9d4929d1d4abd3721a27377369a
lake exe cache get
lake build --wfail
lake env leanchecker JSP000301
```

Keep the committed `lake-manifest.json`; do not run `lake update` when reproducing this exact snapshot. The pinned `.github/workflows/ci.yml` specifies NaNoda and axiom-audit reproduction, including tool revisions.

## Formal statements

`JSP000301.lean` defines `Powerful n` using Mathlib's `Nat.Prime` and the condition that every prime divisor's square divides `n`. `PerfectSquare n` means `∃ m : ℕ, m ^ 2 = n`.

The declarations `JSP000301.jsp_000301_counterexample` and `JSP000301.jsp_000301_disproved` respectively exhibit a positive witness and negate the universal claim. See [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md) for the submitter's comparison, not an independent review.

## Submission status and attribution

The recipient-recommendation issue attempted through the connected integration on September 16, 2026 was rejected with HTTP 403. **No official issue or PR has been filed by that attempt.** The filled [submission draft](SUBMISSION_ISSUE_DRAFT.md) is not a submission receipt.

A formal PR to the designated official repository and official verification are still required unless the Prize confirms its externally peer-verified registration exemption. Our own CI run does not establish that exemption. A fork and maintainer review are pending.

Earlier submissions for the same scoped problem exist. This project claims only the formalization and verification work actually evidenced here, not precedence over those submissions. Any credit, eligibility, tier or payout remains for the Prize to determine.

See [PROVENANCE.md](PROVENANCE.md) for AI assistance and contribution limits.

## Official sources

- [Problem record](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301)
- [Contribution instructions](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md)
- [Selection Rules](https://www.hejustinsun.com/prize/rules)
- [FAQ](https://www.hejustinsun.com/prize/faq)
