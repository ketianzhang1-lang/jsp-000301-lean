# JSP-000399: the 27-element triple-sum exception

## Exact result

This package proves that two different finite subsets of the positive integers, each with 27 elements, have the same multiset of sums of three distinct elements. The result is transported to finite subsets of the complex numbers and proves `not_unique_27 : ¬ Unique 3 27`.

The witness sets are:
```text
A = {20, 28, 32, 34, 35, 67, 70, 71, 73, 77, 85, 103, 105, 106, 109, 110, 112, 117, 118, 120, 124, 148, 156, 160, 162, 163, 195}
B = {5, 37, 38, 40, 44, 52, 76, 80, 82, 83, 88, 90, 91, 94, 95, 97, 115, 123, 127, 129, 130, 133, 165, 166, 168, 172, 180}
```

Both sets have 27 distinct positive elements. There are binomial(27,3) = 2925 triples in each set. Equality is equality of **multisets**, preserving every repeated sum. These are sets, not lists permitting repeated input values.

## Scope and contribution

This completes the specific negative result at cardinality 27. It is partial scope relative to the broad JSP-000399 catalog question. It does not prove the 486-element exception, positive uniqueness criteria, or uniqueness for all sufficiently large cardinalities. It is a formalization of known mathematics, not a new mathematical solution or a claim of global first priority.

The exception at 27 is attributed to D. V. Fomin and O. T. Izhboldin (1994) by the [Formal Conjectures specification](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/494.lean). The original paper has not been independently inspected for this submission. The concrete integer instance here was constructed independently and checked directly.

Prior prize submissions [#23](https://github.com/TheJustinSunPrize/awards/pull/23) and [#127](https://github.com/TheJustinSunPrize/awards/pull/127) cover other cases. The reviewed [plby proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos494.lean) proves the card=2k case. Those contributions are acknowledged and are not re-claimed. Public searches are not an exhaustive priority determination.

## Construction

Set a=(1,2,4,8,16,-31) and b=64. Form the 27 integers consisting of a_i+a_j for i<j and -a_i+b, -a_i-b for each i. Call this intermediate set W. Then A=100+W and B=100-W. The Lean proof verifies the displayed integers directly; it does not assume a general identity for all a and b.

## Formal proof route

1. Compute and kernel-check the cardinalities and inequality of A and B.
2. Enumerate their three-element subsets, sum each subset, and kernel-check multiset equality directly, including multiplicities.
3. Prove that injectively casting a natural-number set into the complex numbers commutes with taking these sum multisets.
4. Apply the supposed uniqueness statement and injectivity of the cast to contradict A != B.

The proof uses `decide +kernel`, not native evaluation. Standard foundational axioms are disclosed by the audit. Independent Python enumeration is a supplemental cross-check, not the proof.

## Reproduction and review

Lean and Mathlib are pinned to v4.34.0; transitive dependency revisions are in lake-manifest.json. From this directory:
```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

See VERIFICATION.md for actual run status and evidence. Cached Mathlib and network access are used. Contributor-run verification is not an organizer award decision or independent human review.

Proposed recipient: RECIPIENT-JSP-000399-KZ-A, confirmation pending. OpenAI ChatGPT assistance is disclosed. Maintainers must assess incremental formalization, attribution, statement fidelity, overlap, priority, and eligibility. No award amount or payment entitlement is asserted.
