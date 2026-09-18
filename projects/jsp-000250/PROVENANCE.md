# Contribution and source provenance

We prepared the original `JSP000250.lean` under GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. Its eleven public
lemmas and theorems are retained byte-for-byte from commit
`567770d9977669a0846c491d0822fda8dddf9011`. They include denominator clearing,
the prime obstruction, the least exception, the explicit logarithmic upper
bound and its unconditional Big-O formulation. Mathematical credit for this
method remains with Erdős and Graham and with Liu and Sawhney.

Our new `JSP000250Complete.lean` contributes ten theorems. They establish exact
equivalence of our finite-set predicate with the imported predicate and its
strictly increasing sequence form, identify the least exceptions for every
natural cutoff including zero, transport the explicit lower-range witnesses,
handle least denominators one and two, derive the strict lower bound, and
combine that bound with our original upper proof. The upper direction of the
complete endpoint invokes our own original theorem, not an imported upper
estimate. We also supply the pinned compatibility port, full-closure audit,
independent-checker script and reproducible build instructions.

The lower-bound mathematics is due to Yang P. Liu and Mehtaab Sawhney,
Theorem 1.6 of *On further questions regarding unit fractions* (2024),
https://arxiv.org/abs/2404.07113. It uses the Croot/Bloom unit-fraction method.
Our integration does not claim new informal mathematics.

The complete lower formalization and its transitive source closure are reused
from `plby/lean-proofs` at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its
[Erdos294 entry](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos294.lean)
credits Codex and GPT-5.6 Sol; relevant source files retain their copyright
notice for Boris Alexeev and author notices for OpenAI Codex. The imported
75-module closure includes Erdős 294, 297 and 285 developments, the
`UnitFractions` library and `PrimeNumberTheoremAnd` analytic dependencies.
Original source headers and all available notices are preserved. Each
compatibility-ported file carries an explicit modification notice. The
`UnitFractions` port traces its Lean 3 declaration surface to the public
[b-mehta/unit-fractions](https://github.com/b-mehta/unit-fractions) development.
Authors of these dependencies, Mathlib, lean4export and NaNoda retain their
respective credit and licenses.

`UPSTREAM.json` records immutable source URLs, Git blob hashes, original
SHA-256 hashes, precise compatibility renames/edits and resulting source
hashes. The bootstrap downloads source, verifies those hashes and applies
only the recorded edits. The upstream license notice and Apache 2.0 text
are included. Sources are fetched into ignored directories; their absence
from the tracked tree is not an omitted mathematical premise.

We claim our original upper formalization, exact model integration and
verification work. We do not claim authorship of the imported lower proof,
first-formalization priority, independent human verification or award
entitlement. Maintainers must assess contribution eligibility under the
current rules; owning this repository does not establish authorship of
imported work.
