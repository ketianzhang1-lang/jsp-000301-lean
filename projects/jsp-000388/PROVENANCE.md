# Contribution, sources and retained attribution

We developed our implementation and integration under GitHub account
`ketianzhang1-lang` with OpenAI ChatGPT/Codex assistance.

## Our original implementation and new work

The parent proof revision is `c32d8195dc69e19d9bcf96987543f306c71749f2`, branch
`jsp-000388-quadratic-obstruction` of `ketianzhang1-lang/jsp-000301-lean`.
`JSP000388.lean` is retained byte for byte. It independently implements the
explicit-difference and boundedness proof for the normalized quadratic family.

We add `JSP000388Complete.lean`: the predicate correspondence, general
translation theorem, all-integer shifted-polynomial consequences, a literal
complete-existence endpoint and a combined existence/obstruction interface.
We also prepare the hash-pinned dependency bootstrap, Lean 4.34 compatibility
port, full verification scripts and statement correspondence documentation.

## Mathematical and formal sources

For the original square obstruction, mathematical credit remains with Milan
Sekanina (1959). For the quadratic obstruction, credit remains with AlphaProof
and Sarosh Adenwalla, following the catalog and the pinned statement reference.
The original formal-statement reference and publication links remain recorded
in `verification/original-provenance.md`.

The affirmative sixth-power development is imported from `plby/lean-proofs`,
branch `main`, exact commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
Its entry is `src/latest/ErdosProblems/Erdos477.lean`, with terminal theorems
`Erdos477.erdos477` and `Erdos477.erdos477_sixth_power`.
The source identifies **Codex** as its formal author and credits Liam Price
(GPT 5.6 Sol Pro), *Large Powers Tile the Integers*, together with the earlier
finite-avoidance criterion from Pengbinghui/pipeline-math.

All imported headers are retained. The repository license notice is preserved
in `UPSTREAM-LICENSE.txt`; imported source is covered by its Apache 2.0 notices.
`UPSTREAM.json` records original source hashes, compatibility edits and resulting
hashes. These edits adapt syntax/library APIs; they do not replace a mathematical
obligation with an assumption. Mathlib and its dependencies retain their licenses.

## Existing prize work and limits of requested credit

[PR #61](https://github.com/TheJustinSunPrize/awards/pull/61), by `KunHcz`, is an
earlier competing quadratic-family submission. The earlier public full
sixth-power formalization is also explicitly acknowledged above.
We request assessment only of our concrete separately implemented obstruction,
translation consequences, interfaces and verification integration.

We do not claim new mathematical discovery, independent authorship of the
sixth-power proof or first-formalization priority for the original problem.
Contributor-run automated checks are not independent human or organizer review.
Acceptance, contribution eligibility and any award decision remain pending.
