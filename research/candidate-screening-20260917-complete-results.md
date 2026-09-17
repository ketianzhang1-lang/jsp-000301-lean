# Candidate screening: complete results, 2026-09-17

This is a research checkpoint, not a proof submission or a request for an award. No new complete solution was obtained during this screening round.

## Decision

Do not treat the prize catalog's `Lean proof: No` label as evidence of an unformalized problem. The six candidates below have public source declaring relevant complete results. They should not be proposed again as easy first-formalization targets without identifying a concrete gap in that source or a genuinely different contribution.

Source inspection is not proof verification. None of these external projects was rebuilt in this round, their dependency closures were not independently checked, and the presence of a declaration or `#print axioms` command is not a successful execution receipt. This screening excludes them from an initial priority-based shortlist; it does not certify their correctness or decide their authors' eligibility.

## Pinned evidence

Official catalog: [TheJustinSunPrize/awards at f4e7173](https://github.com/TheJustinSunPrize/awards/tree/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems).

External source: [plby/lean-proofs at 8822f7d](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems). The public commit API records this revision on 2026-09-15. The local checkout was clean at this revision. The inspected files target Lean/Mathlib 4.33.0.

| Prize ID | Corresponding external source | Endpoint inspected | Selection consequence |
| --- | --- | --- | --- |
| JSP-000383 | [Erdos471.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos471.lean) | `erdos_471`: some finite prime set has unbounded generations under adjoining prime sums of three distinct existing elements. It invokes a separately imported distinct-prime Vinogradov theorem. | The elementary closure induction is already present. Repeating that reduction would not supply a new full proof; the imported analytic theorem must be included in any verification assessment. |
| JSP-000385 | [Erdos473.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos473.lean) | The source states the prime-sum permutation problem for **positive** integers and constructs a spanning ray from finite path extensions. It imports analytic and prime-cluster modules. | A finite prime-sum path is insufficient. A faithful endpoint must prove bijectivity and prime sums for every adjacent pair, with the positive-integer convention explicit. |
| JSP-000628 | [Erdos767.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos767.lean) | `erdos_767`: for `k > 0` and `n >= 3*k+3`, the extremal edge count is `(k+1)*n-(k+1)^2`. The forbidden configuration uses actual simple cycles and distinct incident chord endpoints. | The complete-bipartite lower construction alone would be partial. The source already contains both directions, with a substantial cycle-theoretic dependency chain. |
| JSP-000632 | [Erdos771.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos771.lean) | `erdosF_asymptotic`: `f(n)/(n/log n)` tends to `1/2`. Its exact definition says: for **every positive target m**, there exists a subset of `[1,n]` of the claimed size avoiding m as a subset sum. | Preserve the quantifier order and ambient interval. The catalog's abbreviated wording about an arbitrary integer set cannot be used as the formal statement. A single modular obstruction is not the complete asymptotic result. |
| JSP-000817 | [Erdos984.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos984.lean) | `erdos_984`: one Boolean coloring works for every real epsilon > 0, with a constant A such that every monochromatic progression of positive start a and positive step has length at most `A*a^epsilon`. | The coloring must be chosen before epsilon; constructing a separate coloring for each epsilon weakens the problem. The source already assembles this endpoint from the Hunter-family modules. |
| JSP-000837 | [Erdos1005.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1005.lean) | `erdos_1005`: the relevant Farey separation quantity divided by n tends to `1/4`, with an adapter between two exact definitions. | The file attributes its combined source to Ricky Cipollini and Wouter van Doorn with Aristotle. A copied or ported proof must preserve that attribution; it is not a new solution by this account. |

The other source headers also contain author and license notices. This checkpoint links to those notices rather than transferring mathematical or formalization credit to the submitting account.

## Existing work to avoid duplicating

The live GitHub read also found the user's newer official PRs: [#374, JSP-000303](https://github.com/TheJustinSunPrize/awards/pull/374), [#377, JSP-000295](https://github.com/TheJustinSunPrize/awards/pull/377), [#378, JSP-000017](https://github.com/TheJustinSunPrize/awards/pull/378), and [#379, JSP-000443](https://github.com/TheJustinSunPrize/awards/pull/379). Their submitted scopes remain partial or special-case results as stated in their bodies. They are not new targets for this round.

Earlier exclusions remain in force, particularly the user's abandoned JSP-000617 and JSP-000925 directions. A separate conversation reports ongoing JSP-000906 work; that is a coordination exclusion, not a verified completion claim.

## Gate for a future submission

Before starting another package, identify an exact theorem or a concrete missing verification step, compare it with the original statement and existing source, and explain what this account would add. Reusing an existing proof may support reproducibility work, but does not justify claiming the proof's authorship or first-formalization priority.

The [official introduction](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/docs/about.md) separates catalog flags, candidate records, verification evidence, and announced awards. A green build, an open pull request, or a partial theorem does not establish an award or a right to payment. This checkpoint neither changes any official record nor claims a new prize-eligible contribution.
