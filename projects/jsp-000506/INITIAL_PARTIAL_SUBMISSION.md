# Submission status and prepared PR

The proof and evidence are ready. On September 17, 2026, creating a PR in
TheJustinSunPrize/awards through the GitHub integration failed with HTTP 403,
"Resource not accessible by integration". This is an access limitation, not
an organizer review decision. No official PR or award acceptance is claimed.

The one-file review branch is published at commit
`d89278c887fe0918d0a9dbf276a7eb3b046d5fbf` in ketianzhang1-lang/awards.

[Open the prepared comparison](https://github.com/TheJustinSunPrize/awards/compare/main...ketianzhang1-lang:jsp-000506-heckel-evidence?expand=1) and create a pull request against
`TheJustinSunPrize/awards:main`, using the title and body below. The fork
contains only the new scoped evidence note relative to the checked main.

## Title

JSP-000506: scoped Heckel reduction evidence and eligibility review

## Body

This requests scope and eligibility review of a finite component relevant to JSP-000506 / Erdős 625. The current catalog says **Eligible to claim: No**. This PR does not claim an award, change that marker, or create a verified candidate record.

The new evidence note documents an independently written Lean formalization of Heckel's Proposition 3: if `chi - zeta <= g` has probability at least 999/1000 in a uniform random labelled graph, some interval of length `g` contains `chi` with probability greater than 9/10. Chromatic monotonicity, cochromatic complement symmetry, and `zeta <= chi` are proved from explicit graph definitions.

**Material limitation:** SamPetkov/Erdos already publicly reports a stronger asymptotic formalization. That work is credited and was not copied or imported. This contribution claims no first-Lean priority, new mathematical discovery, or solution of the full problem. Please assess whether the compact finite reduction has any eligible incremental value.

Evidence:
- Tested proof commit: [8b9764f](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/8b9764fd38e85f615b9b871a0e2ac01b7271e952/projects/jsp-000506).
- [Actual successful run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168750399): `lake build --wfail`, `leanchecker --fresh`, and the axiom audit passed.
- Five audited targets report only `propext`, `Classical.choice`, and `Quot.sound`.
- [Pinned verification record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9b703b2b51e613d51cadeb3a46dbbdc4249850fb/projects/jsp-000506/VERIFICATION.md) includes hashes, retained output, reproducibility, and checker limits.

Recipient placeholder: `RECIPIENT-JSP-000506-KZ-A`; written confirmation pending. This is a self-submitted, AI-assisted formalization, not an independent review.

Repository checks against main `f4e7173`: `validate`, `links`, `build`, `check`, `history --base`, and all 22 unit tests passed. Generated data is unchanged. Only one English evidence note is added. Repository checks do not certify the mathematical statement or establish eligibility.
