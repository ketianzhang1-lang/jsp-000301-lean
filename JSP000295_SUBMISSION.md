# JSP-000295: prepared submission

The proof and review package are complete. The connected GitHub integration returned HTTP 403 when asked to open the upstream pull request; no PR was created by that call.

[Open the prefilled official submission page](https://github.com/TheJustinSunPrize/awards/compare/main...ketianzhang1-lang:awards:submit-jsp-000295-weisenberg?expand=1&title=JSP-000295%3A%20Lean%20proof%20of%20the%20known%20square-root%20lower%20bound%20(scoped%20component)&body=%23%23%20Contribution%0AKnown%20lower-bound%20component%20for%20JSP-000295%20%2F%20Erdos%20357%3A%20f(n)%20%3E%3D%202*Nat.sqrt(n)-1%20for%20every%20n%2C%20hence%20(2%2Bo(1))*sqrt(n).%20This%20does%20not%20settle%20f(n)%3Do(n)%20or%20the%20exact%20growth%20rate.%0A%0A%23%23%20Package%20and%20evidence%0A%5BFull%20submission%2C%20scope%2C%20attribution%20and%20verification%5D(https%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fawards%2Ftree%2F9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056%2Fdocs%2Fsubmissions%2Fjsp-000295-kz)%0A%5BSuccessful%20proof%20CI%5D(https%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35171855423)%0A%0A30%20new%20files.%20Lean%204.34.0%20build%20--wfail%2C%20three%20kernel%20replays%2C%20nine%20axiom%20audits%20and%20strict%20NaNoda%20passed%20(13%2C975%20declarations).%20All%2022%20official%20repository%20tests%20and%20validate%2Flinks%2Fbuild%2Fcheck%2Fhistory%20passed.%20Exact%20source%20and%20artifact%20hashes%20are%20recorded.%0A%0A%23%23%20Review%20request%0AMathematical%20credit%3A%20Desmond%20Weisenberg%2C%20following%20the%20pinned%20Formal%20Conjectures%20statement.%20Independently%20written%20OpenAI%20ChatGPT-assisted%20implementation%3B%20original%20statement%20authors%20and%20licenses%20credited.%20No%20global-first%20or%20new-mathematics%20claim.%0AProposed%20recipient%3A%20RECIPIENT-JSP-000295-KZ-A%3B%20confirmation%20pending.%0APlease%20assess%20scope%2C%20attribution%2C%20overlap%20and%20eligibility.%20Contributor-run%20checks%20do%20not%20establish%20an%20award%20or%20payment%20entitlement.) and choose **Create pull request** to complete submission from the authorized GitHub account.

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
