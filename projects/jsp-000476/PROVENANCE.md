# Contribution and source record

We submit this integration under the GitHub account **ketianzhang1-lang**, with
OpenAI ChatGPT assistance. We preserve all upstream authorship and licenses.

The mathematical result is due to Hoi H. Nguyen and Van H. Vu, *Squares in
sumsets*, [arXiv:0811.1311](https://arxiv.org/abs/0811.1311), published in *An
Irregular Mind* (2010), pp. 491–524. The prime-multiple lower-bound construction
is classical and attributed to Erdős. Our earlier squarefree-part classification
does not supply the global upper bound by itself.

## Previously public formal proof

The complete upper and lower asymptotic proof is reused from
[plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587),
commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, under its file-level Apache-2.0
notices. Its Erdős 587 root credits Codex and GPT-5.6 Sol for the formalization,
the Formal Conjectures authors for the statement, and Nguyen–Vu for the mathematics.
We retain those credits and the individual contributor notices in all restored files.

The exact import closure contains 241 source files plus one patch-supplied source file from that repository, 187 from
[CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB/tree/1c1c74664e40071c2c2165bc55ca2616a67ccd6b)
at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, and 14 from
[frenzymath/FormalPantheon](https://github.com/frenzymath/FormalPantheon/tree/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/Warning)
at `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`. The latter two repositories have
Apache-2.0 licenses. AINTLIB's HasseWeil development and FormalPantheon's Waring
development retain their own authorship; repository ownership is not a substitute
for the per-file contributor notices.

`UPSTREAM.json` records the repository, immutable URL, Git blob SHA, original
SHA-256, and restored SHA-256 for every file. `UPSTREAM_PATCHES.json` records the
three existing upstream Lean/Mathlib 4.33 patches. Their names include “linter”,
but the HasseWeil patch also supplies a missing module and substantive proof
repairs. We apply every relevant section, including those repairs; the raw
AINTLIB checkout alone is not the verified dependency. These are **upstream
proof repairs and patches**, not our new proof work. Exact original and final
bytes are identified in the manifest. The reconstruction is tested from an
empty directory before the complete compilation run.

## Our work

- We retain `JSP000476.lean` byte for byte from our previously verified revision
  `4ab28a44e7c89d814699c70f79a0e138f72162e7`.
- We wrote `JSP000476Complete.lean`: equivalence of the two admissibility predicates,
  equality of the extremal quantities, finite-set maximum and witness interfaces,
  monotonicity and the empty interval, the full epsilon formulation, a direct
  original-problem endpoint, and a square-forcing consequence.
- We supply the minimal pinned source closure, reconstruction and audit scripts,
  exact-version verification records, and catalog references.

This is an attributed completion of our submission. It is not a claim that we
discovered the mathematical upper bound or first completed its formalization.
[awards PR #1471](https://github.com/TheJustinSunPrize/awards/pull/1471) also records
the prior plby formalization; our existing PR #372 should be reconciled with it
by the maintainers. We do not create a duplicate submission or a new award claim.
