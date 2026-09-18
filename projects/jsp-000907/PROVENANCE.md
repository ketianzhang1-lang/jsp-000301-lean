# Contribution and provenance

We prepared this contribution under GitHub account `ketianzhang1-lang`, with
OpenAI ChatGPT/Codex assistance. Our source files carry this account credit
and are released under Apache 2.0. The containing repository's historical
MIT license does not replace the licenses attached to these files or their
dependencies.

## Our work

- `JSP000907Construction.lean`: the explicit hub-and-diamond graph over an
  arbitrary base; the local color-forcing argument; three-colorability iff
  the base is two-colorable; the four-color upper bound and exact chromatic
  number for three-chromatic bases. This file imports Mathlib only.
- `JSP000907OddRim.lean`: the arbitrary odd-rim family, its 8m+13 vertex
  count, exact chromatic number four and arbitrarily large instances. It
  uses the credited upstream greedy degree-coloring lemma to three-color
  the base cycle; the forcing argument and specialized construction are ours.
- `JSP000907Witness.lean`: an explicit nine-cycle for every member of our
  family and four distinct, formally checked chords.
- `JSP000907Complete.lean`: equivalence of all-subgraph and induced-subgraph
  local hypotheses, arbitrary real thresholds, a pointwise ten bound for
  any guaranteed threshold, bounded-range and no-divergence consequences,
  explicit r < n <= r+31 counterexample orders, and the combined endpoint.
- The complete source manifest, compatibility port and verification scripts.

The earlier odd-rim research note is retained byte-for-byte from
`bd9e587d1411903124531f14329d8df98b076692`. `ORIGINAL_NOTE_SHA256` checks this.
The note's general upper chord bounds and criticality are not fully
formalized in this package. The code does not assume them. The nine-cycle
theorem proves the presence of four chords, not a universal upper bound on
all cycles. No novelty over the entire mathematical literature is claimed.

## Reused full proof

The full original problem is already formalized in
[plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1091.lean).
We reuse that result and its 38-module local dependency closure. The root
file credits OpenAI Codex. The Brooks development credits Brian Rabern and
Opus 5. The Lean-Proofs Authors, Mathlib contributors and every other author
named in the retained headers keep their original credit.

Mathematical credit belongs to Voss for the affirmative two-chord theorem.
The quantitative counterexample is due to
Boris Alexeev, Moe Putterman, Mehtaab Sawhney, Mark Sellke and Gregory Valiant,
*Short proofs in combinatorics, probability, and number theory II*,
arXiv:2604.06609, Section 4. Rabern and Brooks retain the credits described
in the upstream coloring sources. We claim our own formalization and
integration contributions, not original authorship of these imported proofs.

`UPSTREAM.json` records each original immutable URL, Git blob SHA, original
SHA-256, every compatibility edit and the resulting SHA-256. Nine modules
require compatibility changes; headers include modification notices. The
38 source files total 42,428 lines at the recorded port. `UPSTREAM-LICENSE`
retains the upstream distributor's notice, and `LICENSE` contains Apache 2.0.

We do not claim a new full mathematical solution, first-formalization
priority, independent human verification, organizer acceptance or award
entitlement. Repository ownership is not evidence of authorship of the
imported proof. Reviewers can assess our 29 local theorems and the exact
integration independently from the reused work.
