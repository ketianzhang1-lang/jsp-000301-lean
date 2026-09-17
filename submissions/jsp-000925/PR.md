## Change

Please review an incremental Lean formalization for **JSP-000925 / Erdős 1114**, related to existing-proof registration #24.

For every nonzero real polynomial of degree N+1 with N+1 equally spaced roots and positive spacing, the supplement proves strict outward increase of consecutive derivative-root gaps (excluding the equal central mirror pair), reflection symmetry, and the existence and uniqueness of the derivative root in every consecutive root interval. Degree, translation, spacing, and leading coefficient are arbitrary.

The pinned prior theorem already proves the non-strict inequalities and symmetry while assuming an interlacing derivative-root selector. This submission adds strict phase convexity, strict gap inequalities, and an explicit existence/uniqueness theorem. It does **not** claim new mathematics or first formalization of the entire problem. Mathematical credit remains with Bálint; the imported formal infrastructure remains credited to the pinned plby/lean-proofs development.

- [Review request and proof argument](https://github.com/ketianzhang1-lang/awards/blob/a6402918bd8c3ebd54b31325040fdfd86af1b267/docs/submissions/jsp-000925-strict-kz/REVIEW_REQUEST.md)
- [Exact statement and scope](https://github.com/ketianzhang1-lang/awards/blob/a6402918bd8c3ebd54b31325040fdfd86af1b267/docs/submissions/jsp-000925-strict-kz/STATEMENT.md)
- [Verification report and archived logs](https://github.com/ketianzhang1-lang/awards/blob/a6402918bd8c3ebd54b31325040fdfd86af1b267/docs/submissions/jsp-000925-strict-kz/VERIFICATION.md)

## Record or policy impact

The current catalog says **Eligible to claim: No**. Please assess whether this incremental contribution is substantive and eligible for consideration, or direct it to the appropriate intake location. This PR does not override that status or create a candidate, award, recipient profile, or payment entitlement.

This is a self-submission prepared with OpenAI ChatGPT assistance. Proposed recipient: `RECIPIENT-JSP-000925-KZ-A`, confirmation pending. Attribution and contribution allocation remain for the organizers. The unchanged upstream source is fetched by a checksum-pinned bootstrap and is not redistributed in this diff.

## Checks

- [x] Proof/reproduction files are byte-identical to checked proof commit `7b545f0e021b06d434654b17881c11819f3ff1b7`; published proof source read back and matched.
- [x] [Contributor-run CI 35168402594](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168402594) succeeded: Lean build with warnings as errors, both module kernel replays, eight axiom audits, dependency pins, and rejection of a false arithmetic control.
- [x] Independently implemented NaNoda checked 50,927 declarations in both main theorem dependency closures with no errors and a strict three-axiom allowlist.
- [x] External artifact `10475571672`: 53,524,136 bytes; SHA-256 `bb353673593c587c1770d8f4d4aa96dbc958f266aef195923a5c12618c268534`. Download verified. Its advertised expiry is 2026-12-16; compact logs are also preserved in this PR.
- [x] All 22 existing validator tests passed; `manage.py validate`, `links`, `build`, `check`, and `history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae` passed. Generated JSON is unchanged.
- [x] English documentation, pending recipient placeholder, preserved published records and explicit provenance.

## Reviewer decision

Please assess statement fidelity, the formalization increment, provenance and eligibility. Contributor-run proof checks and repository validation do not constitute organizer certification or permission to pay.
