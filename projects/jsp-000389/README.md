# JSP-000389: factorial residues and classical obstructions

This is a scoped Lean formalization for JSP-000389 / Erdos 478.
It does **not** resolve the open asymptotic conjecture or prove that socialist
primes do not exist. It claims formalization work, not new mathematics.

## Exact statements

Write `A(p) = {n! mod p : 1 <= n < p}` and `C(p) = |A(p)|`.

| Lean declaration | Proven statement |
| --- | --- |
| `factorial_residue_lower_bound` | For every prime p, `p-2 <= C(p)*(C(p)-1)`. |
| `factorial_residue_upper_bound` | For every prime p>5 with `p mod 8 != 5`, `C(p) <= p-3`. |
| `socialist_necessary_conditions` | If p>5 is prime and the residues of `2!,..., (p-1)!` are pairwise distinct, then `p mod 8 = 5` and `(L(p)-2)^2 = -1` in ZMod p, where `L(p) = sum_{k=0}^{p-1} k!`. |
| `socialist_missing_residue` | Under that same hypothesis, the missing nonzero residue is the negative of `((p-1)/2)!`. |

`residueCount` uses literal natural-number remainders. `residueCount_eq`
connects it to the finite-field set used in the proof. All statements have
unrestricted parameters, not a numerical testing cutoff. Natural subtraction
in the first theorem is harmless since every prime is at least two.

## Proof structure

The lower bound injects the indices `2,...,p-1` into ordered pairs of unequal
elements of A(p), using successive factorials. Their quotient recovers the index.
For the obstructions, Wilson's theorem gives the factorial reflection identity.
Pairing reflected indices evaluates the product of the factorial residues.
The sole omitted nonzero residue then determines the modulus-eight restriction.
Summing the residues supplies the left-factorial condition. The upper bound
translates failure of injectivity back to a count of distinct natural remainders.

## Source and attribution

- B. Rokowska and A. Schinzel (1960), *Sur un probleme de M. Erdos*,
  Elem. Math. 15, 84-85: the classical modulus-eight and missing-residue result.
- V. Andrejic and M. Tatarevic (2016),
  [On distinct residues of factorials](https://arxiv.org/abs/1603.04086v1),
  Section 2: exposition of that argument and the left-factorial condition (2.6).
- O. Klurman and M. Munsch,
  [Distribution of factorials modulo p](https://arxiv.org/abs/1505.01198),
  introduction: the elementary successive-factorial quotient lower-bound argument.
  The off-diagonal count here spells out that elementary argument; no novel
  lower-bound priority or their stronger analytic theorem is claimed.

The mathematical credit stays with those authors and the prior work they cite.
This Lean implementation was independently written with OpenAI ChatGPT
assistance under the submitting account's direction. Mathlib supplies Wilson's
theorem, finite-field sums, and standard finite-set and arithmetic lemmas.
No third-party contestant proof is imported or copied. This package is not
independent human review or organizer verification.

## Relation to the original problem

The official catalog asks how many distinct factorial residues occur modulo a
prime. The precise open conjecture is `C(p) ~ (1-1/e)*p` along primes, represented
in Formal Conjectures' Erdos 478 statement. The bounds here do not establish it.
They also do not settle the remaining socialist-prime class `p mod 8 = 5`,
prove the quadratic-character restrictions from the literature, or certify a
large finite computational search. The proof is complete for the stated
components and partial relative to the catalog problem.

No matching JSP-000389 intake was found in the official issue/PR search on
17 September 2026. This is a limited search, not a guarantee of first
formalization, novelty or prize priority. The catalog currently marks the
problem `Progress`, `Lean proof: No`, and `Eligible to claim: No`.

## Reproduction

Lean: `v4.34.0`; Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
All transitive revisions are pinned in `lake-manifest.json`.

```bash
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script compiles with warnings as errors, replays the module with the
bundled checker, checks the eight target axiom closures and dependency pins,
and rejects a false arithmetic statement. The second exports the target
closures to an independently implemented checker (NaNoda), permitting only
`propext`, `Classical.choice`, and `Quot.sound`. Actual results are recorded
separately from these instructions.

## Submission

Proposed recipient: `RECIPIENT-JSP-000389-KZ-A`, confirmation pending.
This self-submission requests review of statement fidelity, attribution,
overlap and formalization-contribution eligibility. It does not change catalog,
candidate, award or recipient records. No approval, award or payment entitlement
is asserted. In particular, eligibility of these scoped classical components
has not been established.

New Lean code and scripts: Apache-2.0. Documentation: CC BY 4.0.
