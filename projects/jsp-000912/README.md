# JSP-000912 / Erdős 1099: complete divisor-gap formalization

This project gives a complete Lean proof of the main existence statement for every real exponent greater than one. The formalization contributor is `ketianzhang1-lang`, with OpenAI assistance. The original source header records authorship.

## Result and contribution

For the complete ascending list of positive divisors of a positive integer n, define

`h_alpha(n) = sum_i (d_(i+1) / d_i - 1)^alpha`.

The main declaration, **JSP912.jsp_000912_full** in [FullProof.lean](FullProof.lean), proves:

```lean
∀ α : ℝ, 1 < α → ∃ C : ℝ, 0 < C ∧
  ∀ M : ℕ, ∃ n : ℕ, 0 < n ∧ M ≤ n ∧ JSP912.hAlpha α n ≤ C
```

The conventional quantifier form is exported as `JSP912.erdos_1099`. The same proof is supplied in five modules ending in [JSP912/Main.lean](JSP912/Main.lean).

Our contribution is an explicit multiscale construction and its Lean implementation: finite mixed-radix divisor grids, dyadic bounds, weighted gap decay, complementary-divisor reflection, and telescoping over every adjacent pair in the complete divisor list. For any integer r ≥ 1 with r(α−1) ≥ 4, the construction gives positive integers N_K satisfying

`K ≤ N_K` and `h_alpha(N_K) ≤ 64 (16r(r+1)+2)^2`.

The parameter K is unrestricted, including zero. Choosing K = M supplies a positive witness beyond every requested cutoff. See [PROOF.md](PROOF.md) for the construction and mathematical argument.

This proves the full main existence question. The separate factorial and least-common-multiple variants are outside the submitted theorem.

## Pinned environment and reproduction

- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- All dependency revisions: [lake-manifest.json](lake-manifest.json).
- Public proof branch: `jsp-000912-complete-proof`.
- Organizer review: [PR #691](https://github.com/TheJustinSunPrize/awards/pull/691).

Check out the full 40-character proof commit cited in the catalog or PR. From `projects/jsp-000912`, with Elan and the pinned toolchain installed:

```bash
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Keep the committed manifest; do not run `lake update` when reproducing this snapshot.

The first script builds the standalone proof and all five modules with warnings as errors, replays all six modules with the bundled Lean checker, checks exact theorem and divisor-list types in both layouts, audits seven transitive axiom closures in each layout, checks actual dependency revisions, and requires rejection of an invalid arithmetic statement. It also checks that the standalone and modular proof bodies agree.

The second script exports the seven audited targets and their dependency closures to pinned NaNoda, allowing only `propext`, `Classical.choice` and `Quot.sound`.

The [verification workflow](../../.github/workflows/jsp-000912.yml) runs these checks and publishes the checked source, commit identifier, manifest and logs. Actual execution results must be read from the linked GitHub Actions run; the presence of a script is not itself evidence that it succeeded.

## Source recovery and compatibility port

The recovered Lean 4.19 source and original contributor-side logs are preserved at [commit 9074d0cebd4e132a6c1fa71c0817693246935398](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/9074d0cebd4e132a6c1fa71c0817693246935398/projects/jsp-000912). Every recovered archive file matched its recorded SHA-256 checksum.

The current source is a mechanical Lean/Mathlib 4.34 compatibility port. See [PORT.md](PORT.md) and [LEAN4_34_PORT.patch](LEAN4_34_PORT.patch). No mathematical definition, theorem statement, construction or hypothesis was changed. Historical Lean 4.19 receipts remain under [evidence/original-4.19](evidence/original-4.19) and must not be presented as receipts for the current version.

## Attribution and prior work

The affirmative mathematical result is due to Michael D. Vose, “Integers with consecutive divisors in small ratio,” Journal of Number Theory 19(2), 1984, 233–238, [DOI](https://doi.org/10.1016/0022-314X(84)90107-0).

The recovered project records that this construction and implementation were developed before inspecting the earlier complete formalization in [plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1099.lean). That implementation uses a different cofinal sequence and credits its own formal authors. This project imports Mathlib and its own modules; it does not import or copy that proof.

Requested credit concerns this formalization and verification work. No mathematical-discovery or first-formalization priority is claimed. Contributor-run checks do not constitute organizer acceptance, independent human review or an award decision.
