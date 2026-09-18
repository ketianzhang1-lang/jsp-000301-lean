# Statement correspondence

JSP-000554 corresponds to Erdős Problem 682. The precise research question is
that almost all consecutive-prime gaps contain an interior natural number whose
least prime factor is at least the gap length. The catalog's short wording
must not be read as a claim about every individual gap.

We use `Erdos682.nthPrime n = Nat.nth Nat.Prime n`, indexed from zero.
`lower_add_gap` proves reconstruction of the next prime without excluding the
first index. `badGap_iff_exceptional` proves that our original `BadGap` predicate
agrees with the absence of the required interior number. Both endpoint
primalities and their consecutivity are proved from the prime enumeration.

`JSP000554.jsp_000554` states the complete natural-density-one assertion and
our necessary-and-sufficient residue criterion for every natural gap length
at least two. The analytic conclusion has no extra unproved hypothesis.
`goodGap_count_ratio_tendsto` and `badGap_count_ratio_tendsto` identify the
literal proportions among the first N prime gaps, tending to one and zero.

Natural density here is an ordinary limit, not only an upper-density statement.
The prime-gap condition is `gap <= minFac m`, as in equation (1.1) of Gafni--Tao.
The stronger strict inequality discussed separately in their Remark 1.1 is
not asserted. The full sharp quantitative bound or a conditional asymptotic
constant is not claimed by this integration. Neither is infinitude of bad gaps.

The residue equivalence retains endpoint primality. Membership in a residue
table by itself is not used to infer primality or infinitely many prime pairs.
The restriction `2 <= h` applies to the residue theorem; the density theorem
uses all indices, including the initial gap of length one.
