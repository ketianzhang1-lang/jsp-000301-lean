# Contribution and reuse record

We prepared the original module `JSP000725.lean` under GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. It remains
byte-identical to `projects/jsp-000725/JSP000725.lean` at original proof commit
`a197ebc6cc3ea878c60db0f2456465cef1e8e09b`. Its ten proved declarations supply
the interval construction, exact witness cardinalities, all-`N` existence, and
the even-length boundary obstruction. That original package explicitly claimed
only partial scope; the present package adds the missing arbitrary-set upper
conclusion through an attributed complete development.

Our new bridge and endpoint prove the exact correspondence between the natural
and integer models and their extremal functions, then establish eventual
optimality of our original explicit witness and the sharp limit. The bridge
includes the empty-subset case and the inverse map from bounded integer sets.
We supply the compatibility port, pinned manifest, and verification scripts.

Mathematical credit remains with Straus for the construction and Deshouillers
and Freiman for the eventual exact theorem. The original paper is
[On an additive problem of Erdős and Straus, 2](https://www.numdam.org/article/AST_1999__258__141_0.pdf),
Astérisque 258 (1999), 141–148, especially pages 141–142.

The full upper proof is reused from `plby/lean-proofs` at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its entry header credits formal work
to Codex and GPT-5.6 Sol and carries copyright (c) 2026 Boris Alexeev. The exact
transitive closure contains 39 modules for Erdős 874 and three supporting
modules for Erdős 13. The unused `CyclicKneser.lean` file is not a dependency.
Source author and license notices are preserved. Mathlib, exporter, and
checker authors retain their respective credits and licenses.

`UPSTREAM.json` records each immutable URL, original Git blob SHA, original
SHA-256, exact identifier renames or text edits, and resulting source SHA-256.
Compatibility edits accommodate Lean/Mathlib 4.34 without weakening statements
or adding axioms. The upstream license notice and Apache 2.0 text accompany the
package. Our original source retains its existing repository license.

We request review of our own formalization and integration contribution. We
do not claim the imported upper proof as ours, new informal mathematics,
first-formalization priority, organizer approval, or award entitlement. An
existing complete upstream formalization is disclosed regardless of whether its
authors have filed a competing award claim. Public source availability does not
by itself establish a prize application or its priority.
