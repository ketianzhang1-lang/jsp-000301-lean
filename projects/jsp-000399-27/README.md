# JSP-000399: exceptional 27-element reconstruction failure

This package proves the known negative component of the set-recovery problem at
cardinality **27** and subset size **3**. It supplies two different finite sets
of 27 **distinct integers**, also interpreted as complex numbers, whose multisets
of sums over all three-element subsets coincide. Every one of the 2,925 triples
is counted, including multiplicities of equal sums.

This does not classify recovery for all cardinalities and subset sizes. It is
partial scope relative to the full JSP-000399 catalog entry. No new solution of
the general problem or established first-formalization priority is claimed.

## Explicit sets

Let

```
A = {-20,-19,-15,-13,-11,-10,-8,-7,-6,-5,-3,-2,-1,
      0,1,2,4,5,6,7,8,9,11,13,15,18,21}
B = {-a : a in A}.
```

Both sets have 27 distinct elements, and they differ: 21 belongs only to A.
The exact triple-sum frequency tables agree. The independent Python diagnostic
finds 105 different sums, from -54 to 54, with zero occurring 69 times.

The numerical construction comes from six integers
`x = (13,-5,2,-15,5,0)` of total sum zero and `y=6`: form the fifteen `x_i+x_j`
for `i<j` and the twelve `-x_i+y` and `-x_i-y`. This construction was inspired by
the 27 weights of the E6 representation. No representation-theoretic assertion
is a premise of the Lean proof; the finite certificate proves the stated result.

## Formal statement and proof

`Adapter.lean` defines `complexSumMultiset A k` by
`(A.powersetCard k).val.map (fun s => s.sum id)`, exactly the mathematical
definition in the Formal Conjectures statement of Erdős Problem 494.

`JSP000399Triple.complex_counterexample` proves, without unproved hypotheses:

```
exists A B : Finset Complex,
  A.card = 27 and B.card = 27 and
  complexSumMultiset A 3 = complexSumMultiset B 3 and A != B.
```

`JSP000399Triple.not_unique_27_triples` gives the corresponding negation of
universal unique recovery. The integer-to-complex adapter proves preservation
of cardinality, inequality, all subsets, sums, and multiset multiplicities.
The finite certificate uses `decide +kernel`. Compilation
and all independent checking statuses must be read in VERIFICATION.md; this
README is not itself a verification receipt.

## Attribution and earlier submissions

The exceptional (27,3) nonuniqueness is classical: Fomin and Izhboldin (1994;
English translation 1995), independently Boman and Linusson (1996). Their
published examples discussed in Fomin's survey allow repeated values. The
particular **distinct-integer numerical witness** in this package was constructed
during this project and is not claimed to be their exact published example.

- [Fomin's survey and attribution](https://arxiv.org/abs/1709.06046)
- [Boman--Linusson primary paper](https://tidsskrift.dk/math/article/view/12583)
- [Official problem catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000399)
- [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/494.lean)
- [Earlier PR23: other counterexample families](https://github.com/TheJustinSunPrize/awards/pull/23)
- [Earlier PR127: positive uniqueness criteria](https://github.com/TheJustinSunPrize/awards/pull/127)
- [Earlier issue330: recovery from n-1 sums](https://github.com/TheJustinSunPrize/awards/issues/330)

The listed prior filings do not claim the (27,3) counterexample; this is a report
of the sources checked, not proof of global priority. Their contributions retain
their original credit.

## Contribution and review

OpenAI ChatGPT assisted construction, code, checking and documentation under the
submitting account's direction. This is a self-submission with an interest in its
assessment. Proposed recipient: `RECIPIENT-JSP-000399-27-KZ-A`, confirmation
pending. No independent human review, official acceptance, award tier, amount,
or payment entitlement is asserted. Mathematical credit remains with the cited
researchers. The organizer must assess the scope, incremental formalization,
attribution, priority and eligibility.

## Reproduction

Use the pinned Lean 4.34.0 toolchain and committed dependency manifest.

```
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Do not update the dependency manifest when reproducing a specified commit.
Cached dependencies and network access are used; an offline full dependency
rebuild is not claimed. Proof verification is separate from repository record
validation and from the organizer's award decision.
