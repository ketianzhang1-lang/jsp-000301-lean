# Provenance and contribution

We prepared this development under GitHub account `ketianzhang1-lang` with
OpenAI ChatGPT/Codex assistance. Our contribution comprises the independent
integer-polynomial seed and separated-exponent construction in `JSP000393.lean`,
the new coefficient-ring and minimum-function integration in
`JSP000393Complete.lean`, the compatibility port, the verification package, and
the later general-field induction/minimum interface in `JSP000393General.lean`.
This is AI-assisted work under the submitting account's direction. Account
ownership alone is not offered as evidence of authorship.

## Source ownership and dependencies

| Component | Attribution and origin |
| --- | --- |
| Explicit 13-term seed with 12-term square; product amplification | Don Coppersmith and James H. Davenport (1991); classical sparse-square context also credits Rényi and Erdős. |
| `JSP000393.lean` | Our independently prepared Lean implementation, first published at `a337720331a34599114a9d4669d6518d5e608f6f`; retained without changes. |
| `JSP000393Complete.lean` | Our coefficient-map bridge, exact minimum-function upper bound, arbitrary-cutoff small-ratio theorem, integer threshold consequence, and combined endpoint. |
| Original rational lower bound and `f(n) → ∞` | Mathematics: Andrzej Schinzel (1987). Formal authors recorded upstream: Codex and GPT-5.6 Sol, in plby/lean-proofs at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. |
| `JSP000393General.lean` | Our 2026-09-19 general-field induction and actual-minimum interface, reusing the attributed generic algebraic lemmas. Selected commit: `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8`; not backdated to the earlier rational package. |
| Polynomial algebra, foundations and tactics | Mathlib and Lean contributors at the locked revisions. |

`UPSTREAM.json` lists every fetched source URL, original SHA-256, mechanical
lemma-name and coefficient-access replacements and resulting SHA-256. The 22 upstream modules are fetched
from the original repository, without removing source author notices. The
upstream license notice is retained in `UPSTREAM-LICENSE.txt`; it identifies
Apache-2.0 licensing for externally sourced files. We do not relicense those
files as our own. Our project retains its original MIT license.

The old source implementation and its earlier checks remain traceable in Git
history. The earlier statements that this project does not import plby applied
to that initial constructive-only revision. The current complete development
explicitly imports and credits that prerequisite.

The earlier rational-proof registration in awards issue #44 predates this
integration. We request assessment of our concrete additional implementation
and integration work; we claim neither new mathematics nor first-formalization
priority for the full result. Maintainer acceptance and prize eligibility are
not established by successful machine checking.

## General coefficient-domain completion

`JSP000393General.lean` adds the general-field Schinzel induction wrapper and minimum/attainment/upper-consequence interface, including the literal complex-coefficient endpoint. It reuses the existing general-field algebraic lemmas in the 22 attributed upstream modules; it does not claim to have independently formalized those lemmas. The original two local proof files and upstream manifest remain unchanged. The completion is prepared under the same submitting account with OpenAI ChatGPT/Codex assistance. Its proof commit and verification date must be identified separately from the original construction and rational-only integration, without any backdated priority claim.
