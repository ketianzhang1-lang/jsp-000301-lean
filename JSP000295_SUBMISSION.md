# JSP-000295: Proof and Prize Recommendation Materials

The Lean formalization and verification of the known square-root lower bound are complete. This contribution covers a known component of the original problem; it does not solve the full problem.

**As of 2026-09-17, this integration returned HTTP 403 (Resource not accessible by integration) when attempting to create both the official pull request and the recipient-recommendation issue. Neither attempt completed a submission.**

[Open the prefilled recipient recommendation form](https://github.com/TheJustinSunPrize/awards/issues/new?template=recommend-recipient.yml&title=%5BRecipient%5D%20JSP-000295%3A%20Lean%20formalization%20of%20the%20known%20lower%20bound&entry=JSP-000295%20%2F%20Erdos%20Problem%20357&recipient=RECIPIENT-JSP-000295-KZ-A&contributions=Self-submission%3A%20Lean%20proof%20of%20the%20known%20lower-bound%20component%2C%20f%28n%29%20%3E%3D%202%2ANat.sqrt%28n%29-1%20for%20all%20natural%20n%2C%20hence%20%282%2Bo%281%29%29%2Asqrt%28n%29.%20This%20does%20not%20solve%20the%20full%20problem%20or%20prove%20f%28n%29%3Do%28n%29.%0A%0AComplete%20scope%2C%20attribution%2C%20evidence%20and%20recommendation%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Fblob%2Fjsp-000295-weisenberg%2FJSP000295_SUBMISSION.md%0A%0APinned%20review%20package%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fawards%2Ftree%2F9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056%2Fdocs%2Fsubmissions%2Fjsp-000295-kz%0A%0ASuccessful%20Lean%2Fkernel%2Faxiom%2FNaNoda%20checks%20%2813%2C975%20declarations%29%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35171855423%0A%0APlease%20assess%20contribution%20eligibility.&confirmation=Pending.%20No%20public%20attestation%20of%20written%20confirmation%20is%20supplied.&conflicts=Known%20mathematical%20result%20credited%20to%20Desmond%20Weisenberg.%20Definitions%20and%20theorem%20type%20adapted%20from%20Formal%20Conjectures%20Authors%20%282025%29%2C%20Apache%202.0.%20Independently%20written%20formalization%20with%20OpenAI%20ChatGPT%20assistance.%20Self-submission%3B%20no%20new-mathematics%2C%20global-first%20or%20award-entitlement%20claim.%20Both%20automated%20PR%20and%20issue%20creation%20returned%20HTTP%20403%3B%20neither%20was%20created.%20Review%20overlap%20and%20exact%20scope%20before%20allocating%20any%20award.)

Sign in with your GitHub account, review the title and all five required fields, then select **Create / Submit new issue**. The prefilled form includes a contribution summary, evidence links, confirmation status and attribution. The full recommendation appears below. If signing in clears the prefilled content, copy the five corresponding sections below into the form. If you have already submitted this contribution manually, use the existing issue to avoid a duplicate submission.

The organizer's [contribution guidelines](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) provide an issue-based route for recommending recipients. The prefilled link uses the official form's field IDs; see the [GitHub form documentation](https://docs.github.com/en/communities/using-templates-to-encourage-useful-issues-and-pull-requests/syntax-for-githubs-form-schema). Submission requests review; the organizer determines prize eligibility.

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

On 2026-09-17, the official repository search for JSP-000295 returned no existing issue or PR. The connected integration returned HTTP 403 for both upstream PR creation and recipient-recommendation issue creation; those calls created neither. This recommendation concerns the same already-public contribution. If a PR is required for intake or code integration, the prepared fork branch is `ketianzhang1-lang/awards:submit-jsp-000295-weisenberg`; please link any eventual PR to this recommendation.

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
