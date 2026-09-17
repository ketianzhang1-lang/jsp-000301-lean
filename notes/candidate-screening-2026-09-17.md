# Justin Sun Prize candidate screening, 2026-09-17

This is a research checkpoint, not a proof or a prize claim. No new complete
formalization was produced in this screening pass.

## Existing work and exclusions

Respect the request not to change JSP-000390 / PR260, and to abandon JSP-000617
and JSP-000925. Other current work to avoid duplicating includes JSP-000301,
000388,000391,000392,000399,000924,000506,000530,000250,000736,000725 and 000780.
Some of these are incomplete or partial in scope; inclusion here does not certify
their prize eligibility.

The completed 27-element JSP-000399 submission is now
[PR357](https://github.com/TheJustinSunPrize/awards/pull/357).
Another submission from the same account,
[PR345](https://github.com/TheJustinSunPrize/awards/pull/345), proves the same
(n,k)=(27,3) nonuniqueness component with positive integer witnesses. Their
mathematical scopes overlap. Different numerical witnesses or checking logs do
not by themselves establish two independent prize contributions. Neither PR was
modified or closed during this screening pass.

## Screening findings

The catalog's 'Lean proof: No' is not sufficient evidence of a missing proof.
Search issue bodies, batched correction issues, source repositories and exact
theorem scope in addition to PR titles.

Examples excluded after checking existing sources or submissions:

| Candidate | Existing work or obstacle |
| --- | --- |
| JSP-000264 | Full-scope submissions PR105 and PR115 |
| JSP-000331 | PR170 covers the eventual Graham gcd bound; the all-cardinalities theorem is a substantial further project |
| JSP-000358 | Full contribution in PR285 |
| JSP-000359 | Existing PR34 |
| JSP-000393 | Full rational-coefficient sparse-polynomial result documented in issue44 / plby |
| JSP-000513 | Existing full-scope PR97 and PR99 |
| JSP-000622 | Existing z(20)=6 contribution in PR332 |
| JSP-000690 | Existing complete finite-certificate PR21, PR35 and PR39 |
| JSP-000715,000751,000788 | Existing complete proofs documented together in issue19 |
| JSP-001014 | Prime and squarefree translate counterexamples already in PR43 |

Read the original statements before using the catalog summaries. For example,
the easy infinite totient family in JSP-000884 does not prove the density-one
statement, and a small finite graph example need not establish an asymptotic
extremal theorem.

## Prospects not yet ready for implementation

- JSP-000331: the full Graham gcd result has a published 38-page proof.
  The already submitted eventual result does not immediately fill the remaining
  finite range. No new proof is claimed here.
- JSP-000838 / Erdos1006: a non-cover graph of girth at least five would give a
  full counterexample. Pretzel's 1987 construction is a possible source, but its
  detailed construction was not retrieved; the accessible abstract does not
  justify a small computational certificate. No graph was guessed or certified.
- JSP-000945: the decisive conditions involve real quadratic fields and class
  number one; a simple prime example does not answer the original problem.

## Why the 486-entry example is not a 486-element Finset proof

The published multiset example has entries
`-7` once, `-4` 56 times, `-1` 231 times, `2` 176 times and `5` 22 times.
It has 486 entries but only 5 distinct values. Its negative has the same multiset of
three-index sums. Independent exact enumeration of multiplicity patterns gives
the following table:

| Sum | Multiplicity |
| --- | ---: |
| -15,15 | 1540 each |
| -12,12 | 40656 each |
| -9,9 | 392161 each |
| -6,6 | 1800568 each |
| -3,3 | 4358893 each |
| 0 | 5826304 |

The total is 19,013,940=`choose(486,3)`. Turning this multiset into a Finset
collapses repeated values. A deformation or a different construction preserving
all triple-sum multiplicities would be needed for 486 distinct values; none was
established in this pass. This is not a claim that such a construction is
impossible.

Sources: [Boman--Linusson primary paper](https://tidsskrift.dk/math/article/download/12583/10599/31540)
and [Fomin survey](https://arxiv.org/abs/1709.06046).

The official [prize overview](https://github.com/TheJustinSunPrize/awards/blob/main/docs/about.md)
separates problem-bank flags, nomination records, verification and announced
awards. Successful automated checking does not itself determine a prize or
payment.
