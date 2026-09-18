# JSP-000554: complete prime-gap density and our exact residue classification

Our endpoint `JSP000554.jsp_000554` in `JSP000554Complete.lean` proves the
complete natural-density-one assertion for rough numbers between consecutive
primes, together with our exact residue classification for every gap length
at least two. The density conclusion has no additional unproved hypothesis.

**The complete hosted verification passed on 2026-09-18** for proof commit
`21fcf006fd68b0bead9f979b704c92032f05cba8`: 54 source modules, 37 axiom audits, six kernel-replay prefixes,
the finite diagnostic and false-arithmetic negative control. Independent
NaNoda checked **76,193 declarations with no errors**. See
[the public run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35367960914) and `VERIFICATION.md` for the exact evidence and limits.

Our original 23 theorems remain byte-identical to the earlier partial proof.
Our 12 integration theorems connect that finite classification to the complete
analytic result and express the density conclusions as literal count ratios.
The analytic proof is an attributed dependency from plby/lean-proofs.
`PROVENANCE.md` and `STATEMENT_FIDELITY.md` distinguish our contribution,
the imported work and the exact quantifiers. The earlier partial proof's
historical description is retained in `INITIAL_PARTIAL_README.md`.

## Reproduce the selected proof

```sh
git clone --branch jsp-000554-residue-reduction https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout 21fcf006fd68b0bead9f979b704c92032f05cba8
cd projects/jsp-000554
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Git, Python 3, Lean/Lake, Rust/Cargo and network access are required. Lean is
pinned to 4.34.0 and all nine dependency revisions are locked. The 51 upstream
source modules are fetched from an immutable revision, hash-verified and
ported using the exact recorded recipe. Modified files retain the original
headers and carry explicit modification notices. The final verification runs
from a clean checkout, without local `--resume` reuse.

All 37 exported theorem closures permit only `propext`, `Classical.choice`
and `Quot.sound`. The independent checker treats any other axiom as an error.
The density theorem includes every prime-gap index; `2 <= h` restricts only
the finite residue equivalence. No claim about every gap or cofinite good
gaps is made.

We request assessment of our finite classification, integration and
verification contribution. Machine checks do not establish first-formalization
priority, independent human review, organizer acceptance or award eligibility.
