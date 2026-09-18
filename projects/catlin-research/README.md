# JSP-000585: complete graph-subdivision bound and our exact Catlin witness

We formalize the explicit 15-vertex Catlin graph C5[K3], prove its chromatic
number is exactly 8, construct a K7 subdivision, and exclude every Kr subdivision
with r > 7. We connect this exact certificate to the full uniform
Erdős–Fajtlowicz upper bound for every finite simple graph with at least two
vertices. The entry theorem is **`JSP000585.jsp_000585`** in
[JSP000585Complete.lean](JSP000585Complete.lean).

For n = |V(G)| >= 2, with sigma(G) the largest complete-graph subdivision order,
the package proves that there is an absolute positive C such that

    chi(G) / sigma(G) <= C * sqrt(n) / log(n).

Our new bridge proves equivalence of the original branch-set/path definition
with the indexed definition used by the general theorem. It handles path
reversal and both empty and nonempty branch sets. We additionally prove

    chi(C5[K3]) / sigma(C5[K3]) = 8/7,
    H(15) >= 8/7,
    C >= (8/7) * log(15) / sqrt(15)

for every constant satisfying the uniform bound. H(n) is the supremum of the
ratios over all graphs on Fin n, and the same uniform bound is proved for H(n).
The finite witness does not establish an exact value of H(15) or an optimal C.

## Our contribution and reused work

We retain our seven original proof modules unchanged, including all 37 public
theorems. We add the subdivision-model equivalence, exact numerical bridge,
extremal formulation, witness consequences, compatibility port and reproducible
verification. The work was prepared under GitHub account `ketianzhang1-lang`
with OpenAI ChatGPT/Codex assistance.

The general upper-bound proof is reused with attribution from
[plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos717.lean).
Its 56-module transitive source closure, including graph-linkage dependencies,
is pinned in [UPSTREAM.json](UPSTREAM.json). We claim our own formalization and
integration work; the imported upper proof retains its authorship. Mathematical
credit remains with Catlin and with Fox, Lee and Sudakov for their respective
results. [PROVENANCE.md](PROVENANCE.md) records the boundaries of the contribution.

## Reproduce

Repository: `ketianzhang1-lang/jsp-000301-lean`; branch: `catlin-sharp-kz`.
From a checkout of the full 40-character proof commit recorded in the catalog:

```sh
cd projects/catlin-research
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Use Lean 4.34.0, the committed nine-package manifest, and a Rust toolchain for
NaNoda. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`.
The bootstrap verifies original and ported source hashes before compilation.
The full verifier compiles 66 modules, audits 61 theorem closures, replays the
proof modules and rejects a false-arithmetic control. The second script checks
all 61 exported targets with pinned NaNoda and a strict axiom allowlist.

Consult [VERIFICATION.md](VERIFICATION.md) for checks actually executed. A
workflow definition alone does not establish a passing run. This package updates
[existing PR #432](https://github.com/TheJustinSunPrize/awards/pull/432).
Maintainers must still assess statement fidelity, attribution, contribution
eligibility and any award claim.

## Proof guide

- [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md): original theorem and exact quantifiers.
- [PROOF.md](PROOF.md): our original colouring and K8 obstruction.
- [SHARP_PROOF.md](SHARP_PROOF.md): explicit K7 witness and exact threshold.
- [JSP000585Bridge.lean](JSP000585Bridge.lean): equivalence of subdivision models.
- [JSP000585Complete.lean](JSP000585Complete.lean): full conclusion and consequences.
- [AuditComplete.lean](AuditComplete.lean): all 61 audited targets.
