# JSP-000476: exact threshold for a classical construction

**Scope: a fully proved family-level classification and a constructive lower bound.
This is not a complete solution of JSP-000476 / Erdős 587 and is not a prize claim.**

Let `A(m,k) = {m, 2m, ..., km}`, with `m > 0`, and write
`m = c²q`, where `c > 0` and `q` is squarefree. The Lean development proves

\[
 A(m,k)\text{ has no nonempty subset with square sum}
 \quad\Longleftrightarrow\quad
 \frac{k(k+1)}2<q.
\]

This includes `k = 0`, composite squarefree multipliers, and the equality boundary.
For a squarefree multiplier `q`, failure of the strict inequality produces a
subset whose sum is **exactly `q²`**. It also proves the uniform finite lower bound

\[
 k^2(k+1)\le N
 \quad\Longrightarrow\quad
 \exists A\subseteq\{1,\ldots,N\},\quad
 |A|=k,\quad A\text{ is square-sum-free}.
\]

The second conclusion follows from Bertrand's postulate, already available in Mathlib.
The complete extremal upper bound for arbitrary sets is outside this project.

## Proof

Put `T = 1 + ... + k`. By induction, every integer from `0` to `T` is a subset
sum of `{1,...,k}`. In the inductive step, a target at most the preceding triangular
sum uses the preceding interval; a larger target uses `k` and a suitable earlier subset.

If `T < q`, each nonempty sum from `A(q,k)` is positive, divisible by `q`, and
strictly less than `q²`. A square `z²` divisible by squarefree `q` has `q | z`;
therefore a positive such square is at least `q²`, a contradiction.

If `T >= q`, choose an index subset with sum `q`. The corresponding multiples
have sum `q²`. Multiplying a set by a positive square preserves whether it has
a square subset sum, which reduces general `m = c²q` to squarefree `q`.

Finally, for `k > 0`, choose a prime `p` with `T < p <= 2T` using Bertrand.
Then `A(p,k)` is square-sum-free, has size `k`, and its largest element is at most
`2kT = k²(k+1)`. The empty set handles `k = 0`.

## Attribution and comparison

The prime-multiple lower-bound construction is classical and attributed to Erdős.
Nguyen and Vu state it in Example 1.2 and explicitly extend it to squarefree
multipliers in Remark 1.3 of
[Squares in sumsets, arXiv:0811.1311v2](https://arxiv.org/html/0811.1311v2).
Their Theorem 1.4 gives the difficult upper bound for arbitrary sets.
**Neither the construction nor its squarefree extension is claimed as new mathematics here.**

Before writing this development, we inspected the existing formalization
[plby/lean-proofs, LowerBound.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587/LowerBound.lean)
(Git blob `36a415f3e989cdaeb32ab0aca6f854cd998c8a2c`).
That file proves prime-multiple sufficiency with `k² < p` and an explicit cube-root
lower bound; the same repository also contains a much larger Erdős 587 development.
This project's changes in scope are the exact converse, equality-boundary witness,
classification using the squarefree part of every positive multiplier, and the
finite bound `k²(k+1) <= N`. These comparisons are against that inspected file,
not a claim that no equivalent theorem exists elsewhere.

This Lean implementation was written for Ketian Zhang with OpenAI ChatGPT
assistance, informed by those sources. No original mathematical discovery, first
formalization priority, exclusive ownership, or award entitlement is asserted.

## Formal statements

- `squareSumFree_multiples_iff`: exact criterion for squarefree multipliers.
- `exists_square_subset_multiples`: explicit square-sum existence at and beyond the boundary.
- `square_part_multiples_iff`: exact criterion for `m = c²q`.
- `exists_classification`: every positive multiplier has this classification.
- `exists_card_squareSumFree`: uniform integer lower bound.

The definitions quantify over **all nonempty subsets**. They use natural-number
squares and positive interval elements. No numerical experiment or conjecture is
assumed in these theorems. `Examples.lean` checks prime, composite, equality, and
nonsquarefree cases.

## Reproduce

From this project directory, with Elan installed:

```sh
lake exe cache get
bash scripts/verify.sh
```

Compiler: Lean `4.34.0`. Mathlib:
`5ed2965256430c3649e86755f9576b54eca72435`, with all transitive package revisions
recorded in `lake-manifest.json`.

The verification script builds with warnings as failures, invokes Lean's bundled
`leanchecker`, checks all 20 project declarations against the transitive axiom
allowlist `{propext, Classical.choice, Quot.sound}`, verifies exact dependency
revisions, and checks that a false arithmetic statement is rejected.
The Python test exhaustively computes subset sums for 1,664 parameter pairs;
it supplements the general proof and is not a proof substitute.

The initial local compilation and kernel checks use a cached toolchain with an
environment compatibility shim for executable-path resolution. The shim does not
alter Lean or its kernel. The GitHub workflow uses the ordinary toolchain instead.
See `VERIFICATION.md` for recorded outcomes.

## Award status

This project does not prove the Nguyen–Vu upper bound for arbitrary subsets and
does not establish the entire catalog problem. A family-level sharp criterion
is not a global extremal answer. Existing formalizations and their authors must
be considered in any priority or eligibility review. No catalog status,
recipient allocation, or official prize claim is changed by this branch.

License: Apache-2.0; the mathematical sources retain their original credit.
