# PR title

JSP-000585: complete uniform graph-subdivision bound with our exact Catlin model bridge

# PR body

## Submission type

- [x] Lean proof or formalization author information

## Problem and proposed change

**Problem ID: JSP-000585 / Erdős 717.** Related earlier issue: #417.

We submit the complete uniform upper-bound theorem for arbitrary finite simple graphs, together with our exact Catlin graph formalization and its connection to the general statement. This replaces the earlier finite-example-only description of this PR.

For every finite simple graph (G) on (n >= 2) vertices, let `chi(G)` be its chromatic number and `sigma(G)` the largest order of a complete-graph subdivision in (G). The submitted theorem proves that an absolute constant `C > 0`, independent of the graph and its order, satisfies

```text
chi(G) / sigma(G) <= C * sqrt(n) / log(n).
```

It also proves the corresponding uniform bound for the extremal function `H(n)`, defined over all graphs on `Fin n`. This is the Erdős–Fajtlowicz upper-bound question resolved by Theorem 1.1 of [Fox, Lee and Sudakov](https://arxiv.org/pdf/1107.1920), page 2. We do not claim the exact best constant or a formal proof of the separate random-graph asymptotic lower estimate.

The current PR diff changes only this catalog entry's **Lean proof** and **Attribution basis** fields. The proof sources, dependencies and verification records are hosted in our external repository.

## Our contribution and attribution

We retain our seven original Catlin proof modules, containing 37 public theorems, unchanged from the earlier verified finite development. They prove that the explicit 15-vertex graph `C5[K3]` has chromatic number exactly 8 and contains a subdivision of `K_r` exactly when `r <= 7`, including an explicit `K7` subdivision.

Our two added modules provide 23 public theorems. They establish the exact equivalence of the finite-branch-set and indexed-path subdivision models, including orientation reversal and the empty case; identify the Catlin invariants in the general model; and derive

```text
chi(C5[K3]) / sigma(C5[K3]) = 8/7,
H(15) >= 8/7,
C >= (8/7) * log(15) / sqrt(15)
```

for every constant satisfying the uniform upper bound. We also provide the compatibility port, pinned source closure, statement correspondence and reproducible verification.

We prepared these contributions under GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance.

The complete general upper-bound proof is reused with attribution from [plby/lean-proofs at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos717.lean), whose entry credits Codex and GPT-5.6 Sol. The full 56-module source closure, author notices, licenses, source hashes and compatibility edits are retained or recorded. Mathematical credit remains with Catlin and with Fox, Lee and Sudakov for their respective results.

[PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/PROVENANCE.md) separates our work from imported work. We do not claim authorship of the imported upper proof, new mathematical discovery or first-formalization priority.

## Proof source

```json
[
  {
    "repository": "https://github.com/ketianzhang1-lang/jsp-000301-lean",
    "branch": "catlin-sharp-kz",
    "commit": "9661ef0f170e750b1ac2153b9017bad86044680c"
  }
]
```

- Complete endpoint: [`JSP000585.jsp_000585` in JSP000585Complete.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/JSP000585Complete.lean).
- Exact model correspondence: [JSP000585Bridge.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/JSP000585Bridge.lean).
- [Original-statement correspondence](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/STATEMENT_FIDELITY.md).
- [README and reproduction instructions](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/6879e0402099fff11a820a60f98896d70c3b9378/projects/catlin-research/README.md).
- [Pinned upstream sources and compatibility edits](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/UPSTREAM.json).
- [Verification record and retained receipts](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/6879e0402099fff11a820a60f98896d70c3b9378/projects/catlin-research/VERIFICATION.md).

The later README and verification commit records the completed run; it does not change the submitted Lean proof sources.

## Verification and reproduction

[Public verification run 35332110641](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35332110641) passed at the exact proof commit above:

- All **66 modules** compiled with warnings treated as errors.
- All **61 target theorem-closure axiom audits** passed.
- Kernel replay covered the 56 imported modules and our nine proof modules.
- All nine pinned dependency revisions were checked.
- The false-arithmetic negative control was rejected.
- **NaNoda checked 48,436 declarations with no errors**, using a hard-error allowlist containing only `propext`, `Classical.choice` and `Quot.sound`; statement printing also succeeded.

The audited proof closures use no `sorryAx`, compiler-trust axiom or added unproved mathematical axiom. NaNoda is a separately implemented checker; these contributor-run checks do not constitute independent human review or organizer approval.

Lean is pinned to **4.34.0** and Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`, with transitive dependency revisions locked. With Git, Python 3, elan and Rust/Cargo installed:

```sh
git clone --branch catlin-sharp-kz https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout 9661ef0f170e750b1ac2153b9017bad86044680c
cd projects/catlin-research
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

## Submission checklist

- [x] We changed only Lean proof information and supporting attribution in the relevant catalog entry.
- [x] We supplied a public repository, named branch, full commit SHA, exact theorem, reproduction instructions and attribution evidence.
- [x] The selected commit proves the complete original uniform upper-bound statement, with no missing proof steps or added unproved assumptions.
- [x] The current PR diff contains no proof source files, archives, binaries or vendored dependencies.
- [x] The selected proof commit is contained in the named branch.
- [x] We updated the existing PR for this contribution.

We request maintainer review of the full statement, our disclosed contributions and their eligibility. No award or payment entitlement is asserted.
