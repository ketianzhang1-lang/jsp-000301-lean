# JSP-000728: Cameron–Erdős lower bound

This project proves, for every natural N including zero, that the number of inclusion-maximal sum-free subsets of {1,...,N} is at least 2^(N/4), with natural-number division (floor).

This is a **known lower-bound component** of JSP-000728. It does not prove an asymptotic upper bound, the exact residue-class constants, or solve the full catalog question. No new mathematics or first-formalization priority is claimed.

## Mathematical source and construction

Cameron and Erdős's odd-pair construction, as reproduced in Section 1, page 2 of Balogh, Liu, Sharifzadeh and Treglown, *The number of maximal sum-free subsets of integers*, arXiv:1409.5661:
https://arxiv.org/pdf/1409.5661

Put m=floor(N/4). For m>0, include 4m and exactly one of each pair {2i+1, 4m-(2i+1)}, for 0<=i<m. Every seed is sum-free. Extend it maximally inside the full interval {1,...,N}. Two different choices cannot have the same sum-free extension: their opposite choices add to 4m, already included. The 2^m binary choices give the bound. For m=0, extend the empty set maximally.

The implementation uses the greatest multiple of four below N. The cited exposition uses the greatest even integer below N; both produce the stated 2^floor(N/4) lower bound.

## Statement fidelity

`SumFree` prohibits x+y in A for every x,y in A, including x=y. `MaximalSumFree` means inclusion-maximal within {1,...,N}, not maximum cardinality. `maximalSets` filters the finite powerset by that predicate. The main theorem is `JSP000728.cameron_erdos_lower_bound`. The general parameter theorem `lower_bound_multiple` works in every interval N>=4m.

## Reproduction

Lean 4.34.0 and the committed dependency manifest are required. Mathlib is pinned to 5ed2965256430c3649e86755f9576b54eca72435.

```sh
cd projects/jsp-000728
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The verification workflow compiles with warnings treated as failures, replays the module with the bundled Lean kernel checker, audits the five target declarations against the standard foundational axioms, checks actual dependency revisions, rejects a false arithmetic control, and runs pinned NaNoda with a strict axiom allowlist. A workflow definition is not evidence of a passing run: consult the actual run and receipt before treating verification as complete.

## Attribution and review

Mathematical credit: Peter Cameron and Paul Erdős. Expository source: József Balogh, Hong Liu, Maryam Sharifzadeh and Andrew Treglown. Mathlib and checker authors retain their respective credits and licenses. This implementation was written with OpenAI ChatGPT assistance under the submitting account's direction.

Proposed formalization contributor: RECIPIENT-JSP-000728-KZ-A, confirmation pending. This is contributor-run checking, not independent human review or organizer certification. No award, payment entitlement, new solution, or global priority is asserted.

An existing same-account branch named jsp-000728-maximal-sumfree was observed at the common base commit a42d756719684060b39799db4f10be5ec7de142b, without a JSP-000728 source file, when this package was prepared. Same-account work on an alternative construction is not a separate reward claim. Only one submission for this lower-bound contribution should be considered.
