# JSP-000399 submission ready

Proof and exact-package checks passed. Official pull-request creation through the connected integration returned HTTP 403 (Resource not accessible by integration); this is not yet an official submission.

[Open prefilled pull request](https://github.com/TheJustinSunPrize/awards/compare/main...ketianzhang1-lang:awards:submit-jsp-000399-27-kz?expand=1&title=JSP-000399%3A%20Lean%20certificate%20for%20the%2027-element%20triple-sum%20exception&body=Submit%20the%20known%2027-element%20triple-sum%20exception%20for%20JSP-000399%20%2F%20Erdos%20%23494.%0A%0APackage%2C%20proof%2C%20attribution%20and%20reproduction%3A%20https%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fawards%2Ftree%2Fcc8d8df2db03f517b7a89f195ecd41bbe898d9b9%2Fdocs%2Fsubmissions%2Fjsp-000399-kz%0A%0ATwo%20distinct%2027-element%20positive-integer%20sets%20have%20the%20same%202925%20triple%20sums%20with%20multiplicities.%20Lean%20transports%20the%20certificate%20to%20the%20exact%20complex-Finset%20specification.%20Partial%20scope%3A%20no%20claim%20about%20cardinality%20486%2C%20positive%20uniqueness%20or%20the%20full%20catalog%20classification.%20Fomin%20and%20Izhboldin%20(1994)%20retain%20mathematical%20credit%3B%20prior%20PRs%20%2323%20and%20%23127%20are%20acknowledged.%0A%0AProof%20CI%20(Lean%20--wfail%2C%20kernel%20replays%2C%20seven%20axiom%20audits%2C%20negative%20control%20and%20NaNoda%3A%207511%20declarations%2C%20no%20errors)%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35168262095%0A%0AExact-package%20preflight%20(22%20official%20tests%2C%20all%20repository%20checks%20and%20source-byte%20comparisons%20passed)%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35168840637%0A%0ARecipient%20placeholder%3A%20RECIPIENT-JSP-000399-KZ-A%2C%20confirmation%20pending.%20OpenAI%20ChatGPT%20assistance%20disclosed.%20Please%20review%20incremental%20formalization%2C%20statement%20fidelity%2C%20attribution%2C%20overlap%2C%20priority%20and%20eligibility.%20Contributor-run%20checks%3B%20no%20organizer%20approval%20or%20payment%20entitlement%20asserted.)

Click **Create pull request** on GitHub. Base repository: TheJustinSunPrize/awards, base branch: main. Head: ketianzhang1-lang/awards, branch: submit-jsp-000399-27-kz.

## Title

JSP-000399: Lean certificate for the 27-element triple-sum exception

## Full description

## Contribution

Submit a complete Lean proof of the known **27-element exception** in JSP-000399 / Erdős #494: two distinct finite subsets of the positive integers have identical multisets of three-element sums. Both sets have 27 distinct entries, and all 2925 sums are preserved with multiplicity. A proved injective-cast adapter transports the certificate to finite subsets of the complex numbers, and Compatibility.lean checks the exact Formal Conjectures definitions.

**Partial scope relative to the full catalog entry.** This does not prove the 486-element exception, positive uniqueness criteria, or eventual uniqueness for general k. Fomin and Izhboldin (1994) retain mathematical credit. The specific integer instance was independently constructed. Existing PRs #23 and #127 and plby's card=2k proof are acknowledged; their cases are not re-claimed. No global first-priority claim is made.

## Source and validation

Proof source: `b1de908cb5d9cb006b54c3d44accceca7a979a96` in `ketianzhang1-lang/jsp-000301-lean`, directory `projects/jsp-000399`.
Proof CI: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168262095

The package is under `docs/submissions/jsp-000399-kz/`. See README.md, PROVENANCE.md and VERIFICATION.md for statements, sources, reproduction, overlap and evidence limitations.

Lean build with `--wfail`, two bundled kernel replays, all seven axiom audits, false-arithmetic negative control, and independent enumeration passed. Strict-allowlist NaNoda checked **7511 declarations with no errors**.

Exact submission commit: `cc8d8df2db03f517b7a89f195ecd41bbe898d9b9`.
Exact-package preflight: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168840637
All 22 official tests, validate/links/build/check/history, byte comparisons with verified proof source, isolated 15-file additive scope and package-local links passed. Official generated data is unchanged.

## Review request

Proposed recipient: `RECIPIENT-JSP-000399-KZ-A`, confirmation pending. OpenAI ChatGPT assistance and the submitter's direct interest are disclosed. Please assess incremental formalization, statement fidelity, attribution, overlap, intake placement, priority and eligibility. Contributor-run checks are not independent human certification or organizer approval. No official catalog, candidate or award records are changed, and no award amount or payment entitlement is asserted.

