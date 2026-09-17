# Statement fidelity: complete minimum-support question

`Erdos485.termCount P` is `P.support.card` for `P : Polynomial ℚ`.
`Erdos485.squareTermCounts n` contains exactly the support sizes of squares of
rational polynomials having `n` terms. `Erdos485.f n` is its natural infimum;
`f_attained` proves this is an attained minimum for every `n`.

The imported complete theorem proves

```lean
Filter.Tendsto Erdos485.f Filter.atTop Filter.atTop
```

All auxiliary Schinzel reduction hypotheses are discharged in the pinned
upstream chain. The final theorem takes no additional unproved assumptions.
This is the main question identified as Erdős 485 / JSP-000393, and includes
the corresponding integer-polynomial lower-bound assertion. Our scope is the
rational/integer formulation; no extension to arbitrary coefficient fields,
optimal quantitative bound, or all-support-size optimal upper bound is claimed.

Our original family remains an actual recursively defined integer polynomial:
`F₀ = 1`, `F_(k+1) = S * expand ℤ 25 F_k`. The square of the seed has degree
24, so the proof of separated exponents applies both before and after squaring.
The source module is unchanged from `a337720331a34599114a9d4669d6518d5e608f6f`.

`integer_support` proves equality of supports after the injective coefficient
map from integers to rationals. `rational_family_counts` then gives exact
counts `13^k` and `12^k` in the same domain as the original minimum. Applying
`f_minimal` yields the genuine minimum bound, rather than a newly defined
surrogate quantity.

`arbitrarily_large_small_ratio` quantifies both the ratio factor `M` and the
cutoff `N`. Its witness has size `n = 13^(12*(M+N+1))`; the proof uses the
already established integer inequality `(k+12)*12^k ≤ 12*13^k`.

`integer_uniform_threshold` proves that every integer polynomial with at least
`2 + 32^(2^B)` terms has a square with more than `B` terms. It follows from
the full imported Schinzel bound, not a hypothesis replacing that bound.

The combined theorem `JSP000393Complete.jsp_000393` includes the original
limit theorem and our constructive consequences. The lower-bound contribution
retains its upstream attribution; the combination is not represented as an
independent new proof of Schinzel's result. Organizer review remains necessary.
