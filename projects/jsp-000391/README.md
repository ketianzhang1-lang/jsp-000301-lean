# JSP-000391: Stoll's general-base digit recurrence

## Our formalization contribution

We provide an independently developed, complete Lean implementation of **Stoll's arbitrary-base digit construction** for JSP-000391 / Erdős Problem 482, with OpenAI ChatGPT/Codex assistance.

Our development contributes:

1. **Complete arbitrary-base coverage.** We prove the construction for every integer radix `g >= 2`, every positive real target, every shift in Stoll's admissible interval, and every digit index.
2. **Correctness from the recursive definition.** We define the alternating floor recurrence from its initial value and prove its closed forms and digit-extraction identities.
3. **Full digit semantics.** We prove normalization into `[1,g)`, bounds for every digit, reconstruction error estimates, and convergence of decoded prefixes to the normalized target.
4. **An explicit existence theorem.** We prove that `e = -1/g` is admissible for every radix, giving a concrete endpoint in `JSP000391.jsp000391`.
5. **Reproducible verification.** We supply pinned dependencies, source hashes, build scripts, Lean checker replay, axiom audits and NaNoda verification.

We request credit for this Lean implementation and verification work. The mathematical construction is Stoll's Theorem 1.3 (2005); our theorem covers all positive real targets, including all positive algebraic targets.

## Mathematical statement and fidelity

Let `m = floor(log_g(w))` and `t = w/g^m`. The formal proof establishes `1 <= t < g`. Set

```
a = g / ((g - 1) * (t + g))
b = (g - 1) * (t + g) = g/a
-1/g <= e < (g + 1)*(g - 2)/g
```

The integer sequence is genuinely defined by recursion, starting with `v(0)=1`:

```
v(n+1) = floor(a*(v(n)+e))                 when n is even
v(n+1) = floor(b*(v(n)+1/(g-1)))           when n is odd
```

The index shift is `v(n) = u_(n+1)` relative to the paper. For every `n >= 0`,

```
v(2*n+2) - g*v(2*n) = digit(n)
```

where `digit(0)=floor(t)` is the leading significant digit and `digit(n+1)=floor(t*g^(n+1))-g*floor(t*g^n)`. These are standard floor-difference radix digits. Leading and fractional positions are not interchanged. For targets with two radix expansions, floor truncation chooses the terminating expansion, not an eventually all-(g-1) expansion.

The proof additionally establishes that every digit is in `[0,g)` and that decoding the first n+1 digits and dividing by g^n converges to t, with error in `[0,g^(-n))`. Thus the label "digit" is supported by bounds and reconstruction, not merely assigned to a new arbitrary sequence. Multiplying by g^m restores the original target w.

`jsp000391` supplies the explicit admissible shift e=-1/g. This proves the parameter conditions are satisfiable for every radix. Real parameters and real floor require Lean's `noncomputable` definitions; this is not an admitted proof or an assumed computational oracle. The result is a mathematical correctness theorem, not a claim of a faster numerical algorithm.

## Proof outline

Define the integer geometric sum G(0)=0 and G(n+1)=g*G(n)+1. Prove `(g-1)*G(n)=g^n-1`. Starting from the specified initial value, paired induction establishes

```
v(2*n+1) = G(n)
v(2*n+2) = floor((t+g)*g^n)
```

The expanding step is an exact algebraic identity. The contracting step uses the two defining floor inequalities, the lower and upper shift bounds, and t>=1. No numerical experiment is used in this induction. Translating the second closed form by the integer g^(n+1) yields the required digit differences. Separate floor estimates prove the digit bounds and truncation error, and an Archimedean bound proves convergence.

## Reproduction

We provide the project on branch `jsp-000391-digit-recurrence`. The verified proof snapshot is `14e5155e68554de4e053e4aacd77095a93e96dd4`; this README revision changes documentation only. Select the full commit recorded in the catalog/PR, then run the following from `projects/jsp-000391` with the pinned toolchain available:

```sh
sha256sum -c SOURCE_SHA256SUMS
lake exe cache get
lake build --wfail
lake env leanchecker JSP000391
lake env leanchecker JSP000391Main
lake env lean Audit.lean
```

The Lean compiler and Mathlib revisions are fixed by `lean-toolchain`, `lakefile.lean`, and the committed `lake-manifest.json`. All imported Mathlib infrastructure remains credited to its contributors. The [full verification scripts](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/56f083c6183e93eeffc334e04e39a26548bfae96/projects/jsp-000391/scripts) additionally check actual dependency revisions, transitive axiom reports, negative controls and NaNoda. The selected target proofs and their full transitive dependencies are independently replayed; no nonstandard axioms are permitted.

See [VERIFICATION.md](VERIFICATION.md) for the exact tested proof commit, actual run results, artifact checksums, retention limits and remaining review boundaries. Two checker implementations run by one contributor are not independent human certification.

## Mathematical references

- [Stoll, Journal of Integer Sequences 8 (2005), Article 05.3.2](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.html), Theorem 1.3 and Section 2.2.
- [Original article PDF](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf).
- [Erdos Problem 482](https://www.erdosproblems.com/482).
- [Pinned prize catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000391).

## Attribution and scope

We developed the Lean implementation from Stoll's mathematical argument, with OpenAI ChatGPT/Codex assistance. We preserve the Mathlib attribution and the original MIT notice in [LICENSE](LICENSE).

Our submitted theorem is the complete arbitrary-base construction described above. The submission does not cover every result in Stoll's papers or classify every possible recurrence. We request review of its correspondence with the catalog's general-base existence question and of our formalization contribution. We make no mathematical-discovery or first-formalization priority claim.

## Verification record

Our [public verification run for the pinned proof snapshot](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35252880778) succeeded at `14e5155e68554de4e053e4aacd77095a93e96dd4`. The earlier [successful run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35157931469) and [VERIFICATION.md](VERIFICATION.md) preserve the detailed verification history.

This README revision changes only the contribution presentation and documentation. The Lean proofs, locked dependencies, verification scripts, workflows and source hashes are unchanged. Organizer acceptance and award eligibility remain subject to review.
