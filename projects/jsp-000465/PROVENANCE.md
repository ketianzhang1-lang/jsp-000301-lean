# Source attribution and our contribution

We record GitHub account `ketianzhang1-lang` as the contributor for the Lean 4.34 compatibility port, dedicated JSP000465 interface, singleton-extremal-number equivalence, extremum attainment, simultaneous separation theorem, direct negation endpoint and reproducible verification package. We developed these additions with OpenAI ChatGPT/Codex assistance.

The quantitative construction and its substantive proof come from the attributed upstream development. Our source uses those proved theorems; we do not reassign their authorship to our account.

## Retained upstream attribution

- Original mathematical proof and original formalization: OpenAI team / Astra
  (internal OpenAI model), as identified by the source headers.
- Primary publication: Chapter 10, Theorem 1.1, of
  [Ten Advances in Mathematics and Theoretical Computer Science](https://cdn.openai.com/pdf/ten-proofs-oai.pdf).
- Original formal source:
  [openai/ten-proofs, pinned commit](https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean).
- Immediate modular source:
  [plby/lean-proofs, pinned commit](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos180).
  Original headers and Apache-2.0 licensing are preserved. `UPSTREAM_SHA256SUMS`
  fingerprints those seven source files; `PORT.patch` records our compatibility edits.
- This package's port, interface, and verification orchestration were prepared
  under the submitting account with OpenAI ChatGPT/Codex assistance.
- [Official PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) already
  registers the full existing source. It expressly does not independently rebuild
  or kernel-replay third-party dependencies. No priority over that registration
  or its original contributors is claimed here.

The original module headers, Apache-2.0 notices, `UPSTREAM_LICENSE_NOTICE`, `UPSTREAM_MODULES.json`, `UPSTREAM_SHA256SUMS` and `PORT.patch` preserve the exact source and compatibility changes. Contributor-run verification supports review; originality, contribution allocation and eligibility remain organizer decisions.
