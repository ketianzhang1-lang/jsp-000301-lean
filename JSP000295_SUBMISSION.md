# JSP-000295: Proof and Prize Recommendation Materials

The Lean formalization and verification of the known square-root lower bound are complete. This contribution covers a known component of the original problem; it does not solve the full problem.

## Submission Status

**Submitted:** [Official recipient recommendation #383](https://github.com/TheJustinSunPrize/awards/issues/383), created on 2026-09-17 at 02:18:25 UTC.

The issue is open. At this check, it contains all five required fields, the contribution scope, attribution and public evidence links, and has no comments. No organizer review decision or award announcement appears in the issue. Continue any follow-up in #383 rather than creating a duplicate recommendation.

The earlier automated attempts to create an upstream pull request and recommendation issue returned HTTP 403 (Resource not accessible by integration). The subsequent creation of #383 completed the recommendation submission. The prepared pull request remains available below if the organizer requests code integration.

The [proof CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423) is complete and successful for proof commit `59c5b5540c469b13e7b4848c7c3fbd17e688f519`.

The organizer's [contribution guidelines](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) provide an issue-based route for recommending recipients. Submission requests review; the organizer determines prize eligibility.

## Full Recommendation

Title: [Recipient] JSP-000295: verified Lean formalization of the known square-root lower bound

### Related problem or entry

[JSP-000295](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000295), corresponding to Erdős Problem 357.

### Recipient placeholder or confirmed public ID

`RECIPIENT-JSP-000295-KZ-A`

### Contributions and evidence

Please review this self-submitted **formalization of the known lower-bound component** for contribution eligibility.

For a strictly increasing integer sequence in [1,n], let f(n) be the maximal length for which different consecutive index intervals have different sums. The supplied Lean proof establishes, for every natural n,
`2 * Nat.sqrt n - 1 <= f n`,
and derives the original known statement
`f(n) >= (2+o(1))*sqrt(n)`.

The proof constructs the 2t+1 consecutive integers from t²+1 to (t+1)² for every natural t. It handles all interval pairs, includes the empty sum, and proves that the admissible-length set is bounded before using its supremum. The compatibility module reproduces the two mathematical definitions and target theorem type from the pinned Formal Conjectures source and applies the proof by definitional equality.

**This does not prove f(n)=o(n), determine the exact growth of f, or solve the full JSP-000295 problem. No change to the whole-problem Progress status or eligibility flag is requested.**

Public evidence:

- [Complete review package, pinned submission commit 9526fbc](https://github.com/ketianzhang1-lang/awards/tree/9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056/docs/submissions/jsp-000295-kz).
- [Proof source, pinned commit 59c5b55](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/59c5b5540c469b13e7b4848c7c3fbd17e688f519/projects/jsp-000295).
- [Successful proof CI run 35171855423](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423).
- [Scope, sources and elementary proof](https://github.com/ketianzhang1-lang/awards/blob/9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056/docs/submissions/jsp-000295-kz/PROOF.md).
- [Actual verification receipt and limits](https://github.com/ketianzhang1-lang/awards/blob/9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056/docs/submissions/jsp-000295-kz/VERIFICATION.md).
- [Original statement source, commit 40e7c98](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/357.lean).

Actual completed verification under pinned Lean 4.34.0 and Mathlib:
- Build with --wfail succeeded (3,095 jobs).
- Three bundled kernel replays and nine target axiom audits passed.
- Only propext, Classical.choice and Quot.sound were allowed.
- Dependency revision checks passed and the false-arithmetic negative control was rejected.
- Strict-allowlist NaNoda checked **13,975 declarations with no errors**, including the original-shape compatibility theorem.
- All 22 official repository tests and validate/links/build/check/history passed for the prepared package.
- Published source bytes, tested source archive and copied package were compared. The downloaded artifact hash and byte count were verified.

[Full artifact 10476748299](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423/artifacts/10476748299): 9,228,096 bytes; SHA-256 `90a76dc095ab57ff3c46dff0573af4a6e7a65873172e3858113a9cf6a034b99b`; scheduled expiration 2026-12-16 01:46:35 UTC. Compact original logs, source and checksums are retained in the pinned review package. Cached imports and two preserved EOF formatting notices are disclosed. No permanent external archive, whole-library source rebuild or independent human certification is claimed.

The package adds 30 files under docs/submissions/jsp-000295-kz/ and changes no existing catalog, candidate, award, profile, schema, validator or test file.

### Confirmation status

Pending. No public attestation of written recipient confirmation is supplied. The placeholder is not a confirmed recipient profile.

### Attribution questions and conflicts

The pinned Formal Conjectures statement attributes the known lower bound to **Desmond Weisenberg**; that mathematical credit is retained. The two definitions and theorem type are adapted from the **Formal Conjectures Authors (2025)** under Apache 2.0. This implementation was independently written with **OpenAI ChatGPT assistance**, under the submitting account's direction. Mathlib infrastructure is acknowledged.

This is a self-submission for review of formalization work. No new mathematics, worldwide first-formalization priority, curator/verifier role, organizer approval, award allocation or payment entitlement is claimed. Please assess exact scope, attribution, overlap and eligibility under the applicable rules.

This contribution has been submitted in [official recommendation #383](https://github.com/TheJustinSunPrize/awards/issues/383). Earlier automated creation attempts returned HTTP 403 and did not themselves create an issue or PR. If a PR is required for intake or code integration, the prepared fork branch is `ketianzhang1-lang/awards:submit-jsp-000295-weisenberg`; please link any eventual PR to #383.

## Prepared Pull Request if Requested

[Open the prefilled official submission page](https://github.com/TheJustinSunPrize/awards/compare/main...ketianzhang1-lang:awards:submit-jsp-000295-weisenberg?expand=1&title=JSP-000295%3A%20Lean%20proof%20of%20the%20known%20square-root%20lower%20bound%20(scoped%20component)&body=%23%23%20Contribution%0AKnown%20lower-bound%20component%20for%20JSP-000295%20%2F%20Erdos%20357%3A%20f(n)%20%3E%3D%202*Nat.sqrt(n)-1%20for%20every%20n%2C%20hence%20(2%2Bo(1))*sqrt(n).%20This%20does%20not%20settle%20f(n)%3Do(n)%20or%20the%20exact%20growth%20rate.%0A%0A%23%23%20Package%20and%20evidence%0A%5BFull%20submission%2C%20scope%2C%20attribution%20and%20verification%5D(https%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fawards%2Ftree%2F9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056%2Fdocs%2Fsubmissions%2Fjsp-000295-kz)%0A%5BSuccessful%20proof%20CI%5D(https%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35171855423)%0A%0A30%20new%20files.%20Lean%204.34.0%20build%20--wfail%2C%20three%20kernel%20replays%2C%20nine%20axiom%20audits%20and%20strict%20NaNoda%20passed%20(13%2C975%20declarations).%20All%2022%20official%20repository%20tests%20and%20validate%2Flinks%2Fbuild%2Fcheck%2Fhistory%20passed.%20Exact%20source%20and%20artifact%20hashes%20are%20recorded.%0A%0A%23%23%20Review%20request%0AMathematical%20credit%3A%20Desmond%20Weisenberg%2C%20following%20the%20pinned%20Formal%20Conjectures%20statement.%20Independently%20written%20OpenAI%20ChatGPT-assisted%20implementation%3B%20original%20statement%20authors%20and%20licenses%20credited.%20No%20global-first%20or%20new-mathematics%20claim.%0AProposed%20recipient%3A%20RECIPIENT-JSP-000295-KZ-A%3B%20confirmation%20pending.%0APlease%20assess%20scope%2C%20attribution%2C%20overlap%20and%20eligibility.%20Contributor-run%20checks%20do%20not%20establish%20an%20award%20or%20payment%20entitlement.) and choose **Create pull request** only if a PR is required; link it to the recommendation issue for the same contribution.

Proof CI: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423

Submission branch: https://github.com/ketianzhang1-lang/awards/tree/submit-jsp-000295-weisenberg

## Full PR description

## Contribution and exact scope

Formalize the known lower bound for JSP-000295 / Erdos 357:
`f(n) >= 2*Nat.sqrt(n)-1` for every natural n, hence
`f(n) >= (2+o(1))*sqrt(n)`.

The proof constructs all 2t+1 consecutive integers from t^2+1 to (t+1)^2.
It proves distinct sums for every consecutive index interval, handles the empty
sum, and bounds the admissible lengths before using their supremum.
Compatibility.lean reproduces the pinned original mathematical definitions and
theorem type, and applies the proof by definitional equality.

**This is the complete known lower-bound component, with partial scope relative
to the original problem. It does not prove f(n)=o(n) or determine its exact growth.**

## Sources, attribution and package

Mathematical credit remains with Desmond Weisenberg, as attributed by the pinned
Formal Conjectures statement. The definitions and theorem type are adapted from
the Formal Conjectures Authors under Apache 2.0. This independently written
implementation was prepared with OpenAI ChatGPT assistance. No new mathematics
or global first-formalization priority is claimed.

30 new files under `docs/submissions/jsp-000295-kz/`; no existing records changed.
Read README.md, PROOF.md and VERIFICATION.md for precise scope and reproduction.
Proof commit: `59c5b5540c469b13e7b4848c7c3fbd17e688f519`.
Submission commit: `9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056`.

## Actual verification

Proof CI: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423

Lean 4.34.0 build --wfail passed (3,095 jobs); all three bundled kernel replays,
nine target axiom audits, locked dependency checks and the false-arithmetic
negative control passed. Strict-allowlist NaNoda checked 13,975 declarations
with no errors, including the original-shape compatibility theorem.

All 22 official repository tests and validate/links/build/check/history passed.
The published diff contains exactly the 30 intended additions. Proof-project
bytes were compared with the pinned GitHub checkout and the tested source
archive. Downloaded artifact 10476748299 is 9,228,096 bytes; SHA-256:
`90a76dc095ab57ff3c46dff0573af4a6e7a65873172e3858113a9cf6a034b99b`.
Compact original logs and checksums are included. Finite artifact retention,
cached imports and two preserved EOF formatting notices are disclosed.

## Review request

Proposed recipient: `RECIPIENT-JSP-000295-KZ-A`; confirmation pending.
Please assess statement fidelity, attribution, contribution, overlap, intake
placement and eligibility. These are contributor-run checks, not independent
human or organizer certification. No prize level, award allocation or right to
payment is asserted.
