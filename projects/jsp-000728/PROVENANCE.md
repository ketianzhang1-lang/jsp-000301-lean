# Attribution, original contribution and reuse

## Our formalization

We prepared the independently written lower-bound module under the submitting
GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. It is
byte-identical to `projects/jsp-000728/JSP000728.lean` at our original proof
revision `91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0`. We prove the classical
odd-pair construction, extension to an inclusion-maximal set and the injection
from binary choices for every natural interval length. The lower bound itself
is due to Cameron and Erdős; we do not claim new informal mathematics.

We add the family/count equivalences, the upper-half powerset injection, the
relative little-o and ratio-limit statements, and the fixed exponential saving
relative to all sum-free sets in `JSP000728Bridge.lean` and
`JSP000728Complete.lean`. These additions connect our lower-bound implementation
to the imported complete upper development without assuming its conclusion.
We also supply the pinned source manifest, compatibility port and verification
workflow. These integration contributions are separate from authorship of the
upstream upper-bound argument.

## Mathematical sources

- Cameron and Erdős: the original counting question and classical lower-bound
  construction. An accessible account appears in Section 1, page 2 of
  [Balogh, Liu, Sharifzadeh and Treglown, arXiv:1409.5661](https://arxiv.org/pdf/1409.5661).
- Tomasz Łuczak and Tomasz Schoen: the original affirmative exponential-saving
  result, [On the number of maximal sum-free sets](https://doi.org/10.1090/S0002-9939-00-05815-9), Proc. Amer. Math. Soc. 129 (2001), 2205–2207.
- József Balogh, Hong Liu, Maryam Sharifzadeh and Andrew Treglown: later sharper
  counting results. Their names appear in the reused entry's informal-author
  header; this package does not claim to formalize all their sharp conclusions.

## Imported formal work and license

We reuse the complete transitive source closure of `ErdosProblems.Erdos877` from
`plby/lean-proofs`, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`:
14 modules under Erdős 877, 23 under Erdős 565, and six under Erdős 76.
The entry header names Codex and GPT-5.6 Sol as formal authors. Source headers
also carry the OpenAI Codex and Lean-Proofs Authors notices. Those notices
remain in every downloaded module. Mathlib and verification-tool authors retain
their respective credits and licenses.

`UPSTREAM.json` records each immutable URL, original Git blob SHA, original
SHA-256, exact compatibility changes and final source SHA-256. The bootstrap
only performs those recorded transformations. Port changes accommodate Lean
4.34/Mathlib APIs and tactic imports; they do not weaken a theorem or introduce
an axiom. The upstream license notice and complete Apache-2.0 text accompany
the package. Our unchanged original module retains the repository's license.

## Earlier work and claim limits

The same upper-bound entry already exists at upstream commit
`33a6b9a285cb64ac276ce4d0b3a4111b82c972b6`, recorded on 2026-08-23, before our
lower-bound submission. Its Git blob `95c2b10d5fd8004181b7ed496918e75d3cfe47db`
is unchanged at the selected later pin. We expressly do not claim the first
formal solution of the original question or ownership of that upper proof.

The precise official PR search for `JSP-000728` on 2026-09-18 returned only our
existing PR #373. This bounded observation does not establish worldwide
priority or imply that an upstream author has no related application. We
acknowledge reused source regardless of prize participation.

The same-account alternative `jsp-000728-maximal-sumfree` branch remains at the
common base `a42d756719684060b39799db4f10be5ec7de142b`; it is not a separate
reward claim. We update PR #373 rather than opening a duplicate. This package
contains substantive original lower-bound and integration code as identified
above; ownership of a repository alone does not establish authorship or award
eligibility. Maintainers determine the originality, contribution scope,
acceptability of the original-statement correspondence and any award outcome.
