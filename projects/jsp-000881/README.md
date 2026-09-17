# JSP-000881 / Erdos 1061: explicit linear lower bound

**Scope: a partial result, not a solution of the open asymptotic conjecture.**

Let sigma(n) be the sum of the positive divisors of n. Let S(x) count **ordered**
pairs of positive integers (a,b) with a+b <= x and
sigma(a)+sigma(b)=sigma(a+b). This package proves, for every real x >= 0,

    S(x) >= (38/135)*x - 76.

It also proves the stronger finite block statement

    S(N) >= 76 * floor(N/270)       (N a natural number),

and the corresponding epsilon formulation of a lower asymptotic coefficient
at least 38/135. It does not assert that S(x)/x has a limit, supply a matching
upper bound, or determine the constant in the conjecture S(x) ~ c*x.

## Proof

Multiplicativity of sigma transports any seed solution (a,b) to (at,bt)
when t is coprime to a, b, and a+b. Use these two elementary seeds:

| Seed | Divisor sums | Sufficient multiplier condition |
| --- | --- | --- |
| (1,2) | 1+3=4 | gcd(t,6)=1 |
| (4,5) | 7+6=13 | gcd(t,30)=1 |

In block k, the first family uses t=90k+r for the 30 residues 1<=r<90
coprime to 6. The second uses t=30k+r for r in
{1,7,11,13,17,19,23,29}. Include the reversed ordered pairs.
These give 60+16=76 different solutions, all with sum less than 270(k+1).
The four possible ratios a:b (1:2, 2:1, 4:5, 5:4) are distinct; positivity
and the separated residue intervals prove injectivity both within and across
blocks. The Lean proof establishes all these facts for arbitrary block indices.

The actual real counting function is tied to the integer count by
`realCount_eq`. This handles the floor, positivity and ordered-pair conventions.

## Main declarations

- `scale_solution`: transport any seed by a coprime multiplier.
- `seed_one_two`, `seed_four_five`: the two infinite families.
- `witness_mem`, `witness_injective`: valid, distinct witnesses.
- `block_lower_bound`: 76*floor(N/270) <= S(N).
- `linear_lower_bound`: 38*N <= 135*S(N)+10222.
- `realCount_eq`: exact agreement with the real-argument count.
- `original_real_lower_bound`: (38/135)*x-76 <= SReal(x), x>=0.
- `asymptotic_lower_bound`: for every epsilon>0, eventually
  38/135-epsilon <= SReal(x)/x.
- `infinitely_many_solutions`: infinitely many ordered positive solutions.

## Sources and attribution

- [Prize catalog JSP-000881](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000881).
- [Erdos Problem 1061](https://www.erdosproblems.com/1061).
- [Formal Conjectures statement and ordered-pair convention](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1061.lean),
  blob e52951b54f525c98b3a10ff28462988ad72cc954, by The Formal Conjectures Authors
  (2026), Apache 2.0; it cites Richard K. Guy, *Unsolved Problems in Number
  Theory* (2004), Problem B15. `SReal` follows this definition.
- Mathlib supplies the divisor-sum function and its classical multiplicativity.

The new proofs were prepared with OpenAI ChatGPT assistance for the submitting
account `ketianzhang1-lang`. The two numerical seeds and multiplicative argument
are elementary; mathematical novelty, an improved best-known bound, and global
first-formalization priority are **not** claimed. No third-party proof code was
copied into the mathematical proof. The verification harness is adapted from
the submitting account's existing JSP-000883 package.

A search of the prize repository for JSP-000881 returned no issue or PR at the
time of preparation (2026-09-17 UTC). This is a limited duplicate check, not a
priority guarantee. The catalog marks the original problem Open and Eligible
to claim: No. Eligibility of this partial formalization must be assessed by the
organizers; this package does not establish prize entitlement.

## Reproduce

Lean v4.34.0; Mathlib v4.34.0, revision
5ed2965256430c3649e86755f9576b54eca72435. Other dependencies are pinned in
`lake-manifest.json`.

```sh
lake exe cache get Mathlib.NumberTheory.ArithmeticFunction.Misc Mathlib.Basic.Real.Basic Mathlib.Data.Rat.Floor Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
python3 scripts/check_counts.py
```

`verify.sh` runs the package build with warnings as failures, two Lean kernel
replays, ten target axiom audits, dependency revision checks and an invalid-proof
negative control. `verify_nanoda.sh` exports four final targets and their full
dependency closures for the separately implemented NaNoda checker, with only
propext, Classical.choice and Quot.sound permitted. These are applicant-run
checks, not designated organizer verification. See `VERIFICATION.md` for the
status of checks actually completed. The dedicated
[cloud run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176439458)
passed all stages, including NaNoda verification of 9,711 declarations.
