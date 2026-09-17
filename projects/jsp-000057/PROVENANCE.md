# Attribution and prior work

The mathematical rank-two argument is elementary and classical. No new
mathematical result or global priority is claimed. The proof code in this
project was independently written for Ketian Zhang with OpenAI ChatGPT /
Codex assistance on September 17, 2026.

The definitions `IsSunflowerWithKernel`, `IsSunflower`, and `Erdos20.f` come
from the Apache-2.0 Formal Conjectures project at commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. See [STATEMENT.md](STATEMENT.md)
for exact source links, [NOTICE](NOTICE) for attribution, and the included
[license](LICENSE-APACHE-2.0). The source module adds the proof and the
finite-set bridge; it does not import the conjecture's unfinished theorem.

Prior public formalization relevant to this problem includes
[HowieHwong/lean-erdos-proofs, Erdos/P20.lean](https://github.com/HowieHwong/lean-erdos-proofs/blob/b8b641ba2d00dc4d1fe205a078a4159372672459/Erdos/P20.lean).
That file supplies the general classical Erdős–Rado factorial upper bound,
and is linked by Formal Conjectures. This submission does not claim that
the sunflower problem previously had no Lean work. No proof code from that
file is copied here. An official-repository search for JSP-000057 returned
no matching PR during preparation; this does not establish worldwide
priority, eliminate independent concurrent work, or establish eligibility.

Dependencies are mathlib and its locked dependencies, under their respective
licenses. Verification uses Lean, lean4export, and NaNoda; these are tools,
not additional mathematical assumptions. Their exact revisions and axiom
policy are in the verification scripts.
