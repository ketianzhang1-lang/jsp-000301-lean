# JSP-000912 / Erdős 1099 — complete Lean proof, not a first-formalization claim

**Date:** 2026-09-17  
**Prepared with AI assistance for:** Ketian Zhang  
**Scope:** the full main existence statement, for every real exponent greater than one.  
**Verification:** the complete standalone source compiled successfully locally with warnings treated as errors; exact-type checks and a transitive axiom audit also passed.  
**Priority:** a pre-existing public full formalization was found after this implementation was completed. This package does **not** satisfy a requirement that the problem have no previous full formalization. No first-solution award claim has been submitted.

## 1. Exact theorem

For the complete ascending list of positive divisors of `n`,

\[
1=d_1<\cdots<d_{\tau(n)}=n,\qquad
h_\alpha(n)=\sum_{i=1}^{\tau(n)-1}(d_{i+1}/d_i-1)^\alpha,
\]

the theorem `JSP912.erdos_1099` proves

```lean
∀ α : ℝ, 1 < α → ∃ C : ℝ, ∀ M : ℕ,
  ∃ n : ℕ, M ≤ n ∧ JSP912.hAlpha α n ≤ C
```

The stronger export `JSP912.jsp_000912_full` additionally proves `0 < C` and `0 < n`. Thus zero, an empty divisor list, or one fixed witness cannot trivialize the result.

This is the **complete main question**, not a theorem restricted to integer exponents, exponents at least two, finitely many integers, a selected subset of divisors, or an assumed unproved construction lemma. The separate factorial and least-common-multiple variants are not claimed.

## 2. Explicit construction and bound

For an integer `r ≥ 1` satisfying `r(α−1) ≥ 4`, write `c=r(r+1)` and set

\[
Q_i=\prod_{j=1}^{r}\left[2^{ij}(2^{ij}+1)\right]^{2^{i+1}},\quad
P_K=\prod_{i=1}^{K}Q_i,\quad
E_K=16c(K+1)2^K,\quad N_K=2^{E_K}P_K.
\]

The proof checks, for every natural `K` including zero,

\[
K\le N_K,\qquad h_\alpha(N_K)\le64\bigl(16r(r+1)+2\bigr)^2.
\]

The proof proceeds through finite mixed-radix grids, dyadic scale bounds, a weighted gap estimate, reciprocal-divisor reflection, and telescoping across the **complete** sorted divisor list. See `PROOF.md` for the mathematical argument.

## 3. What was actually checked

The module version contains 792 lines of Lean source across five files. `FullProof.lean` concatenates the same definitions and proofs into a standalone file that imports only Mathlib, not the project modules.

The standalone file was compiled in a separate directory with

```text
Lean 4.19.0
Lean commit 6caaee842e94
Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b
warningAsError=true
```

`Audit.lean` checks the exact quantifier form, the exact sorted-list/zip definition, the positive-witness form, and prints the transitive axioms of the final theorem and six major intermediate results. Each reports only

```text
[propext, Classical.choice, Quot.sound]
```

There are no unfinished proofs or project-declared mathematical axioms in the proof source. No `native_decide` is used. The result is not merely a green repository-format check or a successfully installed compiler.

**Limits of these checks:** this is contributor-side verification using the standard Lean kernel and pinned precompiled Mathlib dependencies. It is not an independent kernel implementation, an independent mathematical referee report, an organizer verification, a claim of approval under the prize's current minimum-safe-version policy, or a payment decision. The included Lake project configuration is for normal reproduction; the recorded successful check used the standalone compiler procedure in `verify-local.sh`.

## 4. Files

- `FullProof.lean`: self-contained project proof, importing only Mathlib.
- `Audit.lean`: theorem-type, definition, and axiom checks.
- `JSP912/*.lean`: the same proof split into five readable modules.
- `PROOF.md`: mathematical proof and scope discussion.
- `README.zh-CN.md`: Chinese result/status explanation.
- `verify-local.sh`: reproduce the checked standalone procedure with a compatible local compiler and Mathlib installation.
- `lakefile.toml`, `lean-toolchain`: pinned configuration for a conventional Lake checkout.
- `evidence/standalone-verification.log`: actual successful check output.
- `evidence/metadata.json`: versions, commands, scope, and verification limitations.
- `SHA256SUMS`: file hashes, excluding itself.

No compiler binaries, dependency archives, compiled project objects, private account details, or credentials are included.

## 5. Reproduction

With a configured Lean/Mathlib checkout at the pinned revisions:

```bash
bash verify-local.sh /absolute/path/to/lean /absolute/path/to/mathlib4
```

For a new conventional Lake project, after installing Elan:

```bash
lake update
lake exe cache get Mathlib/Analysis/SpecialFunctions/Pow/Real.lean Mathlib/Data/Nat/Log.lean Mathlib/NumberTheory/Divisors.lean Mathlib/Data/Finset/Sort.lean Mathlib/Tactic.lean
lake build FullProof
lake env lean -DwarningAsError=true Audit.lean
```

The second route requires internet access to fetch dependencies and may generate a manifest. The Mathlib revision is pinned in `lakefile.toml`; the exact dependency revisions used for the successful local check are in `evidence/mathlib-dependency-manifest.json`.

## 6. Attribution, prior work, and search limitations

The affirmative mathematical existence result is due to Michael D. Vose, **“Integers with consecutive divisors in small ratio”**, *Journal of Number Theory* 19(2), 1984, 233–238, DOI `10.1016/0022-314X(84)90107-0`.

The present multiscale construction and Lean implementation were developed during this session, before inspecting the following independently published full formalization. It is a different implementation; it is **not** claimed as the first proof of the mathematical theorem or the first Lean formalization.

A later global code search for `erdos_1099` found:

- Repository: `plby/lean-proofs`.
- Pinned revision: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- File: `src/latest/ErdosProblems/Erdos1099.lean`.
- The source exports a full theorem for all real `α>1`, including frequent boundedness along `atTop`, and uses the sequence `2^(1+...+k) * product_{i=1}^k (2^i+1)`.
- The file credits the mathematical result to Vose and formal work to Codex / GPT-5.6 Sol. Its stated toolchain is Lean/Mathlib 4.33.0.

The other implementation was inspected as source but was **not** recompiled in the local 4.19.0 environment. Its public full-scope source is enough to prevent an honest assertion here that no prior full implementation exists.

Before this discovery, a search of all PR states in `TheJustinSunPrize/awards` for `JSP-000912`, `Erdos 1099`, `Erdős 1099`, and `erdos_1099` returned no matches. This illustrates why a negative official-PR search and a catalog flag `Lean proof: No` are insufficient to establish originality or priority.

Primary records:

- https://www.erdosproblems.com/1099
- https://www.erdosproblems.com/latex/1099
- https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000912
- https://doi.org/10.1016/0022-314X(84)90107-0
- https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1099.lean

The package is a complete proof deliverable, **not a claim that the user's originality condition has been met**.
