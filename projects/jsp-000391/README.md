# JSP-000391: Stoll's general-base digit recurrence

## Contribution and review request

This is a Lean formalization of Thomas Stoll's 2005 Theorem 1.3, a general-base digit-generating construction associated with JSP-000391 / Erdos Problem 482. It covers every integer radix g >= 2, every positive real target w, every shift in the theorem's admissible interval, and every digit index. It is not a finite numerical example.

Mathematical discovery belongs to Stoll and the earlier literature. This submission seeks review of a formalization contribution, not a new mathematical discovery. It does not claim to formalize all results in Stoll's 2005 or 2006 papers, classify every possible recurrence, establish global first-formalization priority, or create an entitlement to any award. Please assess scope, attribution, originality of the formalization, and eligibility.

Formalization contributor: **ketianzhang1-lang**, the submitting account, with OpenAI ChatGPT/Codex assistance. The implementation was independently written from Stoll's mathematical argument. The account is credited for the Lean implementation, not for the classical mathematics. The original MIT notice is retained in [LICENSE](LICENSE). No independent human or organizer approval is claimed.

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

Select the full 40-character commit recorded in the catalog/PR on branch `jsp-000391-digit-recurrence`, then run the following from `projects/jsp-000391` with the pinned toolchain available:

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

## References and prior-work screening

- [Stoll, Journal of Integer Sequences 8 (2005), Article 05.3.2](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.html), Theorem 1.3 and Section 2.2.
- [Original article PDF](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf).
- [Erdos Problem 482](https://www.erdosproblems.com/482).
- [Pinned prize catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000391).

A public related formalization exists in [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos482.lean). Its source credits Codex and GPT-5.6 Sol and covers the arbitrary-real **binary** theorem and the original Graham--Pollak square-root-of-two recurrence. That source is acknowledged; no global first-formalization priority for Erdős 482 is asserted here.

The theorem in this project is Stoll's **arbitrary-base** Theorem 1.3, including every integral radix at least two. These are different recurrence constructions. This project does not purport to replace the coefficients of the original Graham--Pollak recurrence with its own coefficients, or to classify every recurrence. The requested catalog update presents this complete general-base construction for review of correspondence with the catalog's general-base existence question. Prior work, overlap and prize eligibility remain for maintainer review.

## Documentation correction

The proof and verification scripts were completed at `56f083c6183e93eeffc334e04e39a26548bfae96`, whose [public CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35157931469) succeeded. Its README still described earlier development. This documentation update corrects that stale status and moves the explanatory verification receipt, source hashes and existing compact logs into this proof repository. All Lean files, locked dependencies, scripts and workflows remain byte-for-byte identical to the tested commit.

[VERIFICATION.md](VERIFICATION.md) distinguishes the historical tested commit from this documentation-only descendant. Repository validation and contributor-run proof checks do not establish organizer acceptance or award eligibility.
