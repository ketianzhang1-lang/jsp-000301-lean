# JSP-000506: full random-graph gap and exact finite-model bridges

We integrate the complete original Erdős 625 statement with our retained
finite concentration proof. The main endpoint is `JSP000506.jsp_000506`:
for every fixed natural threshold, the probability that the chromatic minus
cochromatic number meets that threshold tends to one along all graph orders.
**The complete public verification passed on 2026-09-18 (UTC)**
at proof commit `2aca2f16eba715d7ad672dfa017481b647c00063`. All five compilation units, 49 theorem-closure audits,
four kernel replay prefixes, nine dependency pins and the false-arithmetic
negative control passed. Independent NaNoda checked **60,132 declarations
with no errors**. See [the public run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35395208909) and
[the full receipt](VERIFICATION.md).

## Proof and contribution

Our `JSP000506.lean` preserves all 19 original theorems byte-for-byte. Its
mathematics formalizes Annika Heckel's finite concentration reduction.
Our new `JSP000506Bridge.lean` and `JSP000506Complete.lean` add 26 theorems:

- a bijection between finite edge sets and Mathlib simple graphs;
- equivalence of colourings, cocolourings and both minimum invariants;
- exact equality of rational counting probability and `G(n,1/2)` probability;
- transfer of the quantitative bound, divergence of its positive scale, and
  the original fixed-threshold conclusion along the full sequence;
- vanishing small-gap probability and eventual failure of the earlier
  small-gap premise at every fixed width.

`complete_package` combines the full asymptotic endpoint with the retained
finite theorem. The asymptotic endpoint assumes no small-gap hypothesis.
See [statement correspondence](STATEMENT_FIDELITY.md) and
[contribution provenance](PROVENANCE.md) for exact scope.

The unchanged complete quantitative proof is by **Samuil Petkov**, from
[SamPetkov/Erdos](https://github.com/SamPetkov/Erdos), pinned at
`b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea`, under [CC BY 4.0](UPSTREAM_LICENSE). Its single
self-contained file preserves all 480 embedded source modules. We retain
the license, license-scope notice, citation and immutable source hashes.
Our local Apache 2.0 files do not relicense Petkov's work. We claim our finite
formalization, model/probability bridges, consequences and verification, not
authorship or first-formalization priority for the imported complete proof.

## Reproduce

Use the selected proof commit listed in [VERIFICATION.md](VERIFICATION.md),
with the committed lockfile and Lean toolchain unchanged:

```sh
git clone --branch jsp-000506-complete-kz https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout --detach 2aca2f16eba715d7ad672dfa017481b647c00063
cd projects/jsp-000506
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Lean and Mathlib are fixed to 4.31.0, with nine dependency revisions checked.
The first script compiles five source units, audits 49 theorem closures,
replays four module prefixes through Lean's kernel, and rejects a false
arithmetic negative control. The second exports the same 49 targets to a
pinned independent NaNoda checker. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. The receipt records the successful clean hosted run.

Files prefixed `INITIAL_PARTIAL_` preserve the earlier partial submission.
Their scope statements apply to that historical version. The existing
submission is [awards PR #363](https://github.com/TheJustinSunPrize/awards/pull/363).
Machine verification does not establish maintainer acceptance or award eligibility.

## Navigation for preserved upstream license and citation files

The bootstrap preserves the upstream documents byte-for-byte so their pinned
checksums remain verifiable. In the copied `UPSTREAM_LICENSE_SCOPE.md`, the
relative links named `LICENSE` and `CITATION.cff` refer to the **upstream
repository root**, not to this project's local filenames.

For the retained copies in this project, use
[upstream CC BY 4.0 license](UPSTREAM_LICENSE),
[upstream citation](UPSTREAM_CITATION.cff), and
[upstream license-scope document at its original pinned location](https://github.com/SamPetkov/Erdos/blob/b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea/LICENSE_SCOPE.md).
The project's local `LICENSE` applies to our additions as described in
[PROVENANCE.md](PROVENANCE.md); it does not relicense the upstream proof.

This navigation note changes documentation only. The selected proof commits,
upstream bytes, manifests and verification receipts remain as identified above.
