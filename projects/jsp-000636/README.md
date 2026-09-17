# JSP-000636: multiplicity-antichain and threshold bounds

This package formalizes **Lemma 2.5 and the lower bound of Theorem 1.4**
of Yixin He and Quanyu Tang, *An Erdős–Trotter problem on antichains with
multiplicity r on each occurring level*,
[arXiv:2602.09803v1](https://arxiv.org/html/2602.09803v1).
Mathematical credit remains with these authors and the classical
Erdős–Trotter observation they explain. The Lean implementation was written
with OpenAI ChatGPT assistance. This is a formalization of known results.

## Exact scope

For n >= 4 and r >= 2, an inclusion antichain F of distinct subsets of an
n-element ground set, with at least r members at each occurring size, has
at most n-3 occurring sizes (`size_count_le`). For the original convention
of exactly r members at each occurring size, `exact_multiplicity_card_le`
proves |F| <= r(n-3). The latter accepts Mathlib's `IsAntichain` directly;
`antichain_iff_isAntichain` proves the equivalence with the internal predicate.
Boundary examples establish sharpness at n=4, r=2 and the need for the
hypotheses n>=4 and r>=2.

The new module `Lower.lean` proves, for every r >= 4, the unconditional
critical obstruction

    g(2r+2, r) <= 2r-2 < (2r+2)-3.

Here `extremal n r` is the maximum number of occurring sizes over *all*
finite antichains on `Fin n` satisfying the at-least-r condition. The
family-level statement is `critical_size_bound`; the finite maximum
statement is `extremal_critical_le`.

`IsThreshold r N` means that g(n,r)=n-3 for every n>N.
`threshold_lower_bound` proves that **every such N is at least 2r+2** when
r>=4. Consequently the least such threshold, n₀(r), is at least 2r+2.
This proves the mathematical lower bound in He–Tang Theorem 1.4 without
assuming any part of the critical obstruction. Threshold existence is
not formalized here; the final theorem quantifies over every threshold
rather than defining an infimum of a potentially empty set of thresholds.

For [JSP-000636](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000636),
this is a partial formalization contribution. It does not establish the
paper's eventual-equality construction or upper estimate for n₀(r), the
exact values n₀(2) and n₀(3), or a general determination of n₀(r). The
at-least-r convention is the one used in the paper; its equivalence to
exact multiplicity by thinning is not separately formalized here. The
critical obstruction also applies immediately to exactly-r families.
No new mathematical bound, global first-formalization priority, award
eligibility or payment entitlement is claimed.

## Definitions and proof structure

The ground type is `Fin n`; sets and families use `Finset`, so repeated
copies cannot supply multiplicity. Inclusion is ordinary subset inclusion.
The empty family is allowed. Sizes are counted by `F.image Finset.card`.
`extremal` takes `Finset.sup` over the finite set of all admissible families.

For the universal upper bound, singleton members exclude ground elements
from larger members. Multiplicity excludes a unique largest remaining
member. Complementation handles co-singletons; otherwise the occurring
sizes lie in [2,n-2]. Counting the intervals proves the bound.

For the threshold lower bound, work at n=2r+2 and suppose n-3 sizes occur.
Multiplicity excludes sizes 0 and n; a singleton or co-singleton would
force fewer than n-3 sizes. Thus every size in [2,n-2] occurs. The pairs
in F and the complements of its (n-2)-sets form two cross-intersecting
families, each with at least four pairs. The common-star reduction forces
both families to share a center x.

Let P be the leaves of the pairs in F. Every member containing x and of
size greater than two lies in V=Pᶜ, with |V|<=r+2. The complementary star
forces every 3-set in F to contain x. For an (r+1)-set containing x, if
|V|<=r+1 there is at most one possibility. If |V|=r+2 the set is V minus
one element. Incomparability with two distinct 3-sets forces that missing
element into the intersection of two distinct pairs, of size at most one.
So there is again at most one such middle set. Applying the same argument
to the complement family gives at most one middle set avoiding x. This
contradicts the required r>=4 middle sets. Thus g(2r+2,r)<=2r-2, and any
threshold below 2r+2 is impossible.

This implements the cited common-star argument and a symmetric middle-level
counting argument for the critical value. It does not claim to formalize
all intermediate parameter ranges in the paper's Proposition 3.1.

## Reproduction

Lean and Mathlib are pinned to v4.34.0; `lake-manifest.json` records exact
commits. From this directory:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds both modules with warnings as errors, replays both
with Lean's bundled kernel checker, audits all 38 project theorems, checks
dependency revisions and requires false arithmetic to be rejected. The
second uses the separate NaNoda checker with an explicit three-axiom
allowlist, checking the complete dependency closures of both main bounds
and the boundary examples. Commands are reproduction instructions;
consult the verification receipt for actual run results and limits.

No `sorry`, new axiom, or native decision procedure is used. Small examples
use ordinary kernel-evaluated `decide`.

## Prior art and review request

The earlier universal-bound packet was submitted as official
[PR #382](https://github.com/TheJustinSunPrize/awards/pull/382). This extension
belongs in that same PR and adds the general threshold lower bound.
The inspected plby/lean-proofs snapshot
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e` did not contain an Erdos776 module.
This bounded inspection does not establish global priority. The authors'
public work is credited as prior mathematics, not claimed as our discovery
or imported as a Lean proof.

Please assess the combined known-result formalization contribution under
the current rules, with the unproved parts listed above remaining open in
this packet. Recipient placeholder, if required:
`RECIPIENT-JSP-000636-KZ-A`; confirmation pending.

Source license: Apache-2.0 (LICENSE.LEAN). Documentation: CC BY 4.0.
