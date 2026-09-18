# Contribution and source provenance

We prepared the seven original modules Certificate, GraphCore, Profile,
Subdivision, Colouring, Catlin and Sharp under GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. All seven remain
byte-identical to `projects/catlin-research` at proof commit
`019467ead20f2d6b87e672a1dfef7d5b8886febf`. They contain 37 public theorems,
including genuine graph-path and colouring arguments, the explicit K7 witness,
and the exact subdivision classification. The previous package explicitly
covered only a finite special case.

Our new JSP000585Bridge and JSP000585Complete modules add 23 public theorems.
They prove both directions of the finite/indexed subdivision equivalence,
including orientation reversal, connect the exact Catlin invariants to the
general definition, express the extremal function, and derive constraints from
our original witness. We also provide the compatibility port, full pinned
source manifest, stronger audit coverage and reproducible checker pipeline.

The general upper bound follows the mathematics of Fox, Lee and Sudakov,
Theorem 1.1 of [their paper](https://arxiv.org/pdf/1107.1920), pages 1–2.
The Catlin counterexample is classical. Neither is claimed as new informal
mathematics here.

The complete upper-proof source is reused from `plby/lean-proofs`, commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its entry identifies formal authors
Codex and GPT-5.6 Sol. The 56 imported modules comprise 54 Erdős 717 modules,
Erdos718Core, and Erdős 599 Countable. The latter supplies graph-linkage results
and retains its credits to Ron Aharoni and Eli Berger for informal mathematics
and Codex for formalization. All source headers and notices are preserved.
Mathlib, exporter and checker authors retain their respective credit and licenses.
The upstream license notice and Apache 2.0 license text accompany the package.

UPSTREAM.json records each immutable source URL, Git blob SHA, original SHA-256,
exact compatibility renames/edits and resulting SHA-256. These changes port the
source to Lean/Mathlib 4.34 without weakening theorem statements or adding axioms.
We do not claim authorship of the imported general proof, global first-formalization
priority, organizer acceptance or award entitlement. Its existing public source
is disclosed irrespective of whether its authors have submitted a competing
prize application. Ownership of this repository alone is not evidence of
original authorship of imported work.
