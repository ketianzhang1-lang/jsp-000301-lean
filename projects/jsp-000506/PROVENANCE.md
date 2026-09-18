# Contribution and source provenance

## Our contribution

We prepared this development under GitHub account `ketianzhang1-lang`, with
OpenAI ChatGPT/Codex assistance. `JSP000506.lean` is preserved byte-for-byte
from `612b7cb093f17801ec6c6adf126c23619ad8fbd8`; `ORIGINAL_PROOF_SHA256`
records its checksum. Its 19 lemmas and theorems include our formalization
of Annika Heckel's finite Boolean-cube concentration argument and the graph
specialization for every order and every gap width.

Our two new modules add 26 public theorems. `JSP000506Bridge.lean` proves the
bijection between finite edge sets and Mathlib simple graphs, equivalence
of proper colourings and cocolourings, equality of the two chromatic and
cochromatic numbers, and exact equality of rational counting probability
with the standard binomial-random-graph measure. `JSP000506Complete.lean`
transfers the quantitative theorem, proves that its scale diverges, proves
the original fixed-threshold result along the full sequence, and shows that
the old high-probability small-gap premise eventually fails at every fixed
width. It combines the complete original endpoint with our retained finite
concentration theorem.

The complete result has no additional unproved hypothesis. The hypothesis
in Heckel's finite reduction belongs only to that separately stated finite
theorem; it is not assumed by `JSP000506.jsp_000506`.

## Imported complete proof

**Samuil Petkov**, *Erdős Problem 625: Manuscript and Lean Formalization*,
https://github.com/SamPetkov/Erdos, licensed under **CC BY 4.0**.

We reuse `625/formalization/Erdos625SelfContained.lean` at commit
`b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea`. **No changes were made to this
upstream proof.** Its normalized-LF SHA-256 is
`53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837`.
This one file contains the complete 480-module local source closure, with
module boundaries and original source hashes. Its 89,528 lines remain in
the original order. The exact quantitative constant and full original
asymptotic theorem are Petkov's work, not ours.

`UPSTREAM.json` records the immutable source URLs, Git blob hashes and
SHA-256 hashes. `UPSTREAM_LICENSE`, `UPSTREAM_LICENSE_SCOPE.md` and
`UPSTREAM_CITATION.cff` preserve the original license and attribution terms.
`UPSTREAM_README.md` preserves the upstream scope and verification record.
Our local Apache 2.0 license does not relicense this CC BY 4.0 material.
The public source is reconstructed by `scripts/bootstrap.py`; the tested
source archive includes the reconstructed file.

We use the upstream Lean/Mathlib 4.31.0 environment with all nine package
revisions locked. The earlier finite proof used 4.34.0; its historical
manifest is retained as `ORIGINAL_LAKE_MANIFEST.json`. The original finite
source is rechecked on 4.31.0 without changing its statement or proof bytes.

## Mathematical and foundational credit

The original question is due to Erdős and Gimbel. The finite concentration
reduction is due to Annika Heckel, Proposition 3 of
[On a question of Erdős and Gimbel on the cochromatic number](https://arxiv.org/abs/2408.13839).
The complete quantitative result is credited to Samuil Petkov,
[A Full-Sequence Quantitative Gap Between the Chromatic and Cochromatic
Numbers of a Random Graph](https://arxiv.org/abs/2608.30604).
The mathematical predecessors cited in these sources, Mathlib contributors,
Lean developers and independent checker authors retain their credits.

We claim our finite formalization, model and probability bridges, threshold
consequences, integration and verification. We do not claim a new full
mathematical solution, authorship of the imported proof, first-formalization
priority, independent human review or award entitlement. Repository ownership
alone is not authorship. The upstream manuscript itself notes that external
peer review and community acceptance are not established by its license or
machine checks.

Files prefixed `INITIAL_PARTIAL_` preserve the prior submission history.
Their old no-import and partial-scope statements refer to that earlier
version, not to the integrated endpoint.
