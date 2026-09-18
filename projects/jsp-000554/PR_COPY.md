# PR #369: complete title and body

## Title

Submit JSP-000554 complete prime-gap density proof and exact residue classification

## Body

## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

## Problem and proposed change

We submit a complete formalization package for **JSP-000554 / Erdős 682**, replacing the earlier partial scope of PR #369.

For the zero-indexed sequence of primes `p(n)`, our endpoint proves that the set

```text
{ n : Nat | there exists m : Nat with
    p(n) < m < p(n+1) and p(n+1) - p(n) <= minFac(m) }
```

has natural density one. Equivalently, the proportion of exceptional gaps among the first `N` consecutive-prime gaps tends to zero. This is the original almost-all-gaps assertion resolved by Gafni and Tao in [Rough numbers between consecutive primes](https://arxiv.org/abs/2508.06463), Theorem 1.1. The statement includes all indices, including the first gap from 2 to 3. It does not assert that every gap, or every sufficiently late gap, has the property. No Hardy–Littlewood hypothesis is assumed.

Our final theorem also retains our exact necessary-and-sufficient residue classification for every gap length `h >= 2`, with both endpoint primalities. It combines the complete density conclusion with the finite classification already developed in this submission.

The catalog diff updates only **Lean proof** and **Attribution basis** for JSP-000554. We remove the earlier proof packet from the awards repository's current diff while retaining its history. The proof source, dependencies and verification scripts belong in the linked proof repository.

## Our contribution and attribution

We retain our original `JSP000554.lean` byte-for-byte from commit `2a6c737b5fb409a5600918cc5a2bab0a8dd174bb`. Its 23 public theorems prove the uniform residue equivalence, the necessary start-size condition, the exact finite counting identity, and complete residue tables and gap classifications for lengths 2, 4, 6, 8, 10 and 12.

Our 12 integration theorems in `JSP000554Complete.lean` identify our endpoint-based `BadGap` predicate with the actual consecutive-prime-index exception, transport density one and zero to our definitions, express both conclusions as limits of literal prefix-count ratios, and connect the indexed exceptions to our original residue classifier. The final endpoint invokes our retained all-gap residue theorem together with the complete analytic result. We supply the pinned source closure, recorded Lean compatibility port, statement correspondence and reproducible verification.

We prepared this contribution under GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. The mathematics is due to Ayla Gafni and Terence Tao and the predecessors cited in their paper. We reuse the complete analytic formalization and its 51-module transitive closure from [plby/lean-proofs at the pinned revision](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos682.lean), whose Erdős 682 entry credits Codex and GPT-5.6 Sol as formal authors. The PrimeNumberTheoremAnd, UnitFractions, Formal Conjectures, Mathlib and other upstream contributors retain their respective credits. Original source headers and licenses are preserved; modified source files carry explicit compatibility-port notices, and all exact changes and hashes are recorded.

We claim our finite classification, statement bridges, integration and verification work. We do not claim original authorship of the imported analytic proof, new informal mathematics, first-formalization priority or independent human verification. [Our provenance record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/66542c86a00ecedf4d59bd3df0a6c05748e48cb2/projects/jsp-000554/PROVENANCE.md) distinguishes these roles. Repository ownership alone is not presented as authorship or award entitlement.

## Proof source

```json
[
  {
    "repository": "https://github.com/ketianzhang1-lang/jsp-000301-lean",
    "branch": "jsp-000554-residue-reduction",
    "commit": "21fcf006fd68b0bead9f979b704c92032f05cba8"
  }
]
```

- Complete endpoint: [`JSP000554.jsp_000554`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/21fcf006fd68b0bead9f979b704c92032f05cba8/projects/jsp-000554/JSP000554Complete.lean).
- Explicit limits: `JSP000554.goodGap_count_ratio_tendsto` and `JSP000554.badGap_count_ratio_tendsto`, in the same file.
- Original finite formalization: [`JSP000554.lean`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/21fcf006fd68b0bead9f979b704c92032f05cba8/projects/jsp-000554/JSP000554.lean).
- [README and build instructions](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/66542c86a00ecedf4d59bd3df0a6c05748e48cb2/projects/jsp-000554/README.md).
- [Original-statement correspondence](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/66542c86a00ecedf4d59bd3df0a6c05748e48cb2/projects/jsp-000554/STATEMENT_FIDELITY.md).
- [Verification record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/66542c86a00ecedf4d59bd3df0a6c05748e48cb2/projects/jsp-000554/VERIFICATION.md).

The complete density conclusion has no added unproved analytic premise. Endpoint primality and consecutivity follow from the prime enumeration, and the correspondence with our `BadGap` predicate is proved. The condition `2 <= h` restricts the finite residue equivalence only; the density assertion covers every prime-gap index. The roughness comparison is `gap <= minFac(m)`, as in equation (1.1) of the source paper.

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

Lean is pinned to 4.34.0; Mathlib and all nine dependency revisions are locked. The independent checker script also requires Rust/Cargo and pins lean4export and NaNoda. Bootstrap verifies immutable original-source hashes and the exact resulting compatibility-port hashes.

The [complete hosted verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35367960914) passed on 2026-09-18 for the exact proof commit above. All **54 modules** compiled with warnings treated as errors. All **37 axiom audits**, the six proof-module kernel replays, the finite cross-check and the false-arithmetic negative control passed. Independent NaNoda checked **76,193 declarations with no errors**, with a hard-error allowlist containing only `propext`, `Classical.choice` and `Quot.sound`. The checked theorem closures do not depend on `sorryAx` or replacement axioms. The tested source, logs, printed target statements and exported proof closure are archived in the run artifact.

Local awards-repository validation, link/history checks, generated-data consistency checks and all 22 unit tests passed. The upstream PR workflows currently report `action_required` and need maintainer attention before they run. These repository checks validate the submission format.

We request maintainer review of the full statement and our disclosed contribution. Successful machine verification does not establish organizer acceptance or award eligibility.

## Submission checklist

- [x] We changed only Lean proof information and supporting attribution in the relevant catalog.
- [x] We supplied the evidence required for this change.
- [x] The submitted Lean development covers the complete stated result at the specified commit, without `sorry`, `admit` or replacement axioms standing in for proof steps.
- [x] This PR contains no proof source files, archives, binaries or vendored dependencies.
- [x] The named branch contains the full proof commit selected for review.
