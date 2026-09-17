## Contribution

For JSP-000140 / Erdos 136, this package proves the classical lower-bound component with strictness: for every n >= 4 and every symmetric k-coloring of K_n in which each four-element vertex subset sees at least five colors,

`5*(n-1) < 6*k`, hence `floor(5*(n-1)/6)+1 <= k`.

The final theorem uses the standard vertex-subset condition. All n and k are quantified; this is not a finite search. The matching asymptotic upper bound and the full catalog problem are outside scope.

## Evidence

16 new files under `docs/submissions/jsp-000140-kz/`; no existing records or generated data change.

- [Pinned submission package](https://github.com/ketianzhang1-lang/awards/tree/8b29986405c1ab235cc7955ce4c42737951be377/docs/submissions/jsp-000140-kz).
- Tested proof commit: `e3191a77503c145dde16a2b4e4a9489a92947812`.
- [Completed proof/evidence package](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/3e732841177d41a5dd37766510788dcc027ae38f/projects/jsp-000140).
- [Dedicated successful cloud verification](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178843250): build with warnings as errors, two kernel replays, ten axiom audits, dependency-revision checks and an invalid-proof negative control passed. NaNoda checked 6,554 declarations with no errors.
- Lean v4.34.0; pinned Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The only audited/permitted axioms are propext, Classical.choice and Quot.sound.
- Artifact ID 10479915118; 4,572,004 bytes. API-reported ZIP SHA-256: `3854184ba587692eeb85b38e73196d0605aa15b312719aa5518679c257429eb0`. Retention and verification limits are disclosed in VERIFICATION.md; full decoded logs are also committed.
- Organizer validate/links/build/check, all 22 unit tests, and history against main `f4e7173d89dfe91022a185427d63452c8ffbf6ae` passed locally. Submitted files were compared byte-for-byte with the completed package.

## Attribution, scope and requested review

The lower-bound mathematics is classical; the sources and attribution to Erdos-Gyarfas and Erdos-Elekes-Furedi are in README.md.

**Existing formalization is expressly disclosed:** [plby/lean-proofs already has a public Erdos136 entry and lower-bound module](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean). This package is separately written against Mathlib and imports none of that repository. It claims neither new mathematics, an improved best-known bound nor first-formalization priority.

Proposed formalizer: `RECIPIENT-JSP-000140-KZ-A`, confirmation pending. Prepared with OpenAI ChatGPT assistance. Applicant-run automated checks are not independent human review or organizer approval.

Please assess statement fidelity, the separate implementation's contribution in view of prior work, and any applicable recognition. The catalog currently marks Eligible to claim: No. No eligibility change, award or payment entitlement is asserted. Please redirect the proposed intake location if needed.
