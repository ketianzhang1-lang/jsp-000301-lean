# Statement and mathematical correspondence

[Original problem](https://www.erdosproblems.com/939) and
[pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/939.lean).

The catalog entry is [JSP-000780](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000780).
Its one-sentence description does not cover every variant on the original page.
This submission targets `erdos_939.variants.finite`, using r=6; it does not
claim to resolve the whole catalog entry.

| Original component | This package |
| --- | --- |
| `Nat.Full r n := ∀ p ∈ n.primeFactors, p^r ∣ n` | `FactorFull r n`, same formula |
| `Finset.Coprime S := S.gcd id = 1` | `S.gcd id = 1` directly |
| `S.card = r - 2` | Same condition in `OriginalSolutions r` |
| Positive, distinct summands | Positive membership condition and `Finset`, with card 4 proved |
| The sum is r-full | Same condition in `OriginalSolutions r` |
| Universal finiteness for all r ≥ 4 | Negated by `not_finite_for_every_r` |

`SixFull n` initially uses all prime divisors. `sixFull_iff_factorFull` proves
its equivalence to the source's prime-factor-list definition, including n=0.
Solutions separately require positive summands; the construction has positive
sum, so no vacuous zero case contributes.

Coprimality is **collective**, as in the pinned original definition. The
summands are not pairwise coprime: the last three share factors. Strengthening
the problem to pairwise coprimality would invalidate this claim.

The source repository contains unfinished statements with `sorry`. It is not
imported by this proof. The localized definitions and their checked equivalence
are included here; no unfinished theorem is used as a dependency.

## Proof

The binomial identity gives
`(x−y)^6 + 12x^5y + 40x^3y^3 + 12xy^5 = (x+y)^6` for x≥y.
The fixed coefficients factor as
`12*30^6=2^8*3^7*5^6`,
`40*30^18=2^21*3^18*5^19`, and
`12*30^30=2^32*3^31*5^30`.
Multiplication by the appropriate powers of a preserves six-fullness.
Since gcd(a,30)=1, x−y is coprime to x, y and 12. Consequently the first
and second summands are coprime, which proves the collective gcd is 1.
The inequality x>1000y separates all four summands. Finally a, x and (x+y)^6
increase strictly with t; equality of representing sets would imply equality
of their sums. These facts give both infinitude results.
