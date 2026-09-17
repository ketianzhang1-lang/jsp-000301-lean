# JSP-000883: Ready-to-Submit English Materials

The known Monier factorial-bound formalization, infinite family and verification package are complete.

**Submission status:** On 2026-09-17, the connected GitHub integration returned HTTP 403 (`Resource not accessible by integration`) when asked to create the official recommendation issue. That call created no issue. The official repository search immediately before the attempt found no existing JSP-000883 issue or PR.

[Open the prefilled official recipient recommendation form](https://github.com/TheJustinSunPrize/awards/issues/new?template=recommend-recipient.yml&title=%5BRecipient%5D%20JSP-000883%3A%20verified%20Lean%20proof%20of%20Monier%27s%20bound%20and%20an%20infinite%20family&entry=JSP-000883%20%2F%20Erdos%20Problem%201063&recipient=RECIPIENT-JSP-000883-KZ-A&contributions=Self-submission%3A%20Lean%20formalization%20of%20Monier%27s%20known%20bound%202%2Ak%20%3C%3D%20n%28k%29%20%3C%3D%20k%21%20for%20every%20k%3E%3D3.%20Every%20N%3Da%2Ak%21%2C%20a%3E%3D1%2C%20has%20exactly%20one%20descending%20factor%20that%20fails%20to%20divide%20choose%28N%2Ck%29%2C%20namely%20N.%20This%20gives%20infinitely%20many%20starting%20points%20and%20proves%20attainment%20of%20the%20original%20minimum.%0A%0AScope%3A%20does%20not%20prove%20or%20improve%20Cambie%27s%20stronger%20bound%20or%20solve%20the%20full%20problem.%0A%0AComplete%20recommendation%20and%20attribution%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Fblob%2Fjsp-000883-monier%2FJSP000883_SUBMISSION.md%0A%0APinned%20evidence%20package%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fawards%2Ftree%2F2dbfbe7bafd10b892218350bd1d434e211f0cfcf%2Fdocs%2Fsubmissions%2Fjsp-000883-kz%0A%0ASuccessful%20Lean%2C%20kernel%2C%20axiom%20and%20independent%20NaNoda%20checks%20%286%2C675%20declarations%29%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35174825512%0A%0AAll%2022%20repository%20tests%20and%20five%20validation%20commands%20passed.%20Please%20review%20contribution%20eligibility.&confirmation=Pending.%20No%20authorized%20public%20attestation%20of%20written%20confirmation%20is%20supplied.&conflicts=Known%20factorial%20bound%3A%20Jean-Marie%20Monier%20%281985%29.%20Definition%20and%20theorem%20type%3A%20Formal%20Conjectures%20Authors%20%282026%29%2C%20Apache%202.0.%20Independently%20written%20OpenAI%20ChatGPT-assisted%20formalization.%20Self-submission.%20No%20new-mathematics%2C%20global-first%2C%20independent-reviewer%20or%20award-entitlement%20claim.%20Review%20scope%20and%20overlap%20before%20any%20award.)

Sign in with your GitHub account, review the title and all five required fields, and select **Create / Submit new issue**. The short prefilled form links the complete recommendation below and the immutable evidence package. If signing in clears the fields, copy the corresponding five sections below. If you have already submitted this contribution, use the existing issue rather than creating a duplicate.

The [organizer's contribution guidelines](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) provide a recipient-recommendation issue route. Submission requests review; it does not establish acceptance or an award.

## Verified Result and Evidence

For every `k >= 3` and `a >= 1`, `N=a*k!` has exactly one descending factor that fails to divide `choose(N,k)`, namely `N`. This proves the known `2*k <= n(k) <= k!` bound and infinitely many admissible starting points. The open stronger-bound problem remains unresolved by this package.

- [Pinned 36-file review package](https://github.com/ketianzhang1-lang/awards/tree/2dbfbe7bafd10b892218350bd1d434e211f0cfcf/docs/submissions/jsp-000883-kz).
- [Successful cloud verification](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35174825512): Lean build, three kernel replays, nine axiom audits and independent NaNoda (6,675 declarations).
- All 22 official repository tests and validate/links/build/check/history passed.
- Published source, tested source archive and all published package blobs were compared.
- Mathematical attribution and AI assistance are disclosed in the recommendation.

## Full Recipient Recommendation

Title: [Recipient] JSP-000883: verified Lean proof of Monier's bound and an infinite family

### Related problem or entry

[JSP-000883](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000883), corresponding to Erdős Problem 1063.

### Recipient placeholder or confirmed public ID

`RECIPIENT-JSP-000883-KZ-A`

### Contributions and evidence

Please review this self-submitted **Lean formalization of the known Monier factorial-bound component** for contribution eligibility.

For every integer `k >= 3` and positive integer `a`, put `N = a*k!`. The proof establishes `N >= 2*k` and that exactly one of `N, N-1, ..., N-k+1` fails to divide `choose(N,k)`: the exception is `N` itself. It follows that the original least-starting-point function satisfies `2*k <= n(k) <= k!`, and there are infinitely many admissible starting points for every such k.

The proof explicitly establishes nonemptiness and attainment of the original least-element definition. The compatibility module reproduces the pinned definition and Monier theorem type and applies the proof by definitional equality. No unproved conjecture file is imported.

**This does not prove Cambie's stronger least-common-multiple bound, improve it, classify all starting points, or solve the entire original problem. No change to the catalog's Progress status or eligibility flag is requested.**

- [Complete review package, pinned commit 2dbfbe7](https://github.com/ketianzhang1-lang/awards/tree/2dbfbe7bafd10b892218350bd1d434e211f0cfcf/docs/submissions/jsp-000883-kz).
- [Proof source, pinned commit d951a58](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/d951a581d98d209c168ec4066af97df52a7a9498/projects/jsp-000883).
- [Successful CI run 35174825512](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35174825512).
- [Verification receipt and limits](https://github.com/ketianzhang1-lang/awards/blob/2dbfbe7bafd10b892218350bd1d434e211f0cfcf/docs/submissions/jsp-000883-kz/VERIFICATION.md).
- [Elementary proof, scope and sources](https://github.com/ketianzhang1-lang/awards/blob/2dbfbe7bafd10b892218350bd1d434e211f0cfcf/docs/submissions/jsp-000883-kz/PROOF.md).
- [Pinned original statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean).

Completed verification under Lean 4.34.0 and locked Mathlib:
- Build with `--wfail` passed: 3,095 jobs.
- Three bundled kernel replays, nine target axiom audits, dependency checks and the false-arithmetic negative control passed.
- Only `propext`, `Classical.choice` and `Quot.sound` were allowed.
- Independent strict-allowlist NaNoda checked **6,675 declarations with no errors**.
- All **22 official repository tests** and validate/links/build/check/history passed.
- All 11 published proof/workflow blobs, all 10 tested source-project files and all 36 published package blobs matched the prepared bytes. The package adds 36 files and changes no existing records.

The downloaded full artifact is 4,046,754 bytes, SHA-256 `4c8f827bc74dfdaa72dfa2f75e28b21d28db7954195703033e658cb1218755b1`. Its scheduled expiration is 2026-12-16 02:32:45 UTC. Compact original logs, source and checksums are retained in the pinned package. Cached imports, infrastructure notices and finite artifact retention are disclosed. No whole-library rebuild or independent human review is claimed.

### Confirmation status

Pending. No authorized public attestation of written recipient confirmation is supplied. The placeholder is not a confirmed public profile.

### Attribution questions and conflicts

Mathematical credit for the known factorial bound remains with **Jean-Marie Monier (1985)**. The definition and theorem type are adapted from **The Formal Conjectures Authors (2026)** under Apache 2.0. The independently written implementation was prepared with **OpenAI ChatGPT assistance**, under the submitting account's direction. Mathlib infrastructure is acknowledged.

This is a self-submission for review of formalization work. No new mathematics, worldwide first-formalization priority, curator/verifier role, organizer approval, award allocation or payment entitlement is claimed. Please assess scope, attribution, overlap and eligibility.

At the submission check, the official repository search for JSP-000883 returned no existing issue or PR. If code integration is required, the prepared fork branch is `ketianzhang1-lang/awards:submit-jsp-000883-monier`; any eventual PR should be linked to this recommendation as the same contribution.

## Prepared Pull Request if Requested

[Open the prefilled pull request page](https://github.com/TheJustinSunPrize/awards/compare/main...ketianzhang1-lang:awards:submit-jsp-000883-monier?expand=1&title=JSP-000883%3A%20verified%20Monier%20bound%20and%20infinite%20factorial%20family%20%28known%20component%29&body=Please%20review%20the%20known%20Monier%20factorial-bound%20formalization%20for%20JSP-000883%20%2F%20Erdos%201063.%0A%0AFor%20every%20k%3E%3D3%2C%20all%20positive%20multiples%20of%20k%21%20are%20admissible%2C%20giving%202%2Ak%20%3C%3D%20n%28k%29%20%3C%3D%20k%21%20and%20infinitely%20many%20starting%20points.%20This%20does%20not%20prove%20Cambie%27s%20stronger%20bound%20or%20solve%20the%20full%20open%20problem.%0A%0AComplete%20scope%2C%20attribution%2C%20evidence%20and%20actual%20verification%3A%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fawards%2Ftree%2F2dbfbe7bafd10b892218350bd1d434e211f0cfcf%2Fdocs%2Fsubmissions%2Fjsp-000883-kz%0A%0ASuccessful%20Lean%20build%2C%20three%20kernel%20replays%2C%20nine%20axiom%20audits%2C%20strict%20NaNoda%20%286%2C675%20declarations%29%2C%20all%2022%20repository%20tests%20and%20five%20validation%20commands.%0Ahttps%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35174825512%0A%0AMathematical%20credit%20remains%20with%20Monier.%20Statement%20authors%20and%20Apache%202.0%20retained.%20OpenAI%20ChatGPT%20assistance%20disclosed.%20Recipient%20placeholder%20RECIPIENT-JSP-000883-KZ-A%3B%20confirmation%20pending.%20Please%20assess%20incremental%20formalization%20eligibility.%20No%20award%20entitlement%20claimed.%20Link%20this%20PR%20to%20any%20existing%20recommendation%20issue%20for%20the%20same%20contribution.).

Use this if a PR is requested for intake or code integration. Link it to any existing recommendation issue for the same contribution. A separate PR is not a separate reward claim.

Prepared branch: [submit-jsp-000883-monier](https://github.com/ketianzhang1-lang/awards/tree/submit-jsp-000883-monier).
