# Original statement and formal correspondence

JSP-000250 asks about the least denominator that cannot occur in a sum of
distinct positive unit fractions equal to one, with all denominators at most
N. The complete quantitative result selected for formalization is Theorem 1.6
of Liu and Sawhney, *On further questions regarding unit fractions* (2024):
https://arxiv.org/html/2404.07113v1 . The source states a lower
bound of order N / (log N (log log N)^3 (log log log N)^O(1)) and an upper
bound of order N / log N. It does not state an exact asymptotic equivalent.

| Mathematical object | Lean representation |
| --- | --- |
| Cutoff and least denominator | `N t : Nat` |
| Distinct denominators with minimum t and maximum at most N | `JSP000250.Representable N t` |
| Exact sum one | A finite sum of rational reciprocals, with positive denominators |
| Increasing sequence form | `representable_iff_increasing_sequence`, using `Fin (k+1)` and `StrictMono` |
| Least positive forbidden denominator | `JSP000250.firstException N`, defined by a proved existence statement |
| Exact correspondence of the extremal values | `firstException_eq_firstForbidden`, valid also at N = 0 |
| Lower comparison function | `JSP000250.lowerProfile N`, with exponent 20 on the triple logarithm |
| Full endpoint | `JSP000250.jsp_000250` |
| Source's existential-constant form | `JSP000250.liu_sawhney_resolution` |

The complete endpoint proves, for every sufficiently large natural N,

    (1/1000000) * N / (log N * (log log N)^3 * (log log log N)^20)
        < t(N) <= 128 * N / log N.

Both constants and the exponent are explicit; the onset threshold is not.
The eventual quantifier ranges over all sufficiently large natural N, not
over a subsequence. The representation theorem also supplies every positive
least denominator below the displayed lower cutoff, including the cases
one and two. No restriction to prime denominators is imposed in the lower
bound. Prime witnesses are used only in our upper-obstruction proof.

The final theorem has no unproved Fourier, density, smoothness, or
representation premise. All such ingredients of the imported lower proof
are included in the pinned source closure. Intermediate conditional lemmas
are used with their hypotheses proved. Completeness and intended semantics
remain subject to maintainer review in addition to machine checking.
