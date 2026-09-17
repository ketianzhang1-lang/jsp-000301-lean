# JSP-000476: all positive steps, exact square-subset-sum criterion

This package independently formalizes a classical lower-bound construction for
[JSP-000476](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000476),
[Erdős Problem 587](https://www.erdosproblems.com/587).
It proves an exact criterion for the construction and the stronger property of
avoiding every perfect-power subset sum. It does **not** prove the Nguyen–Vu
upper bound or the complete asymptotic solution of the original problem.

## Revision 2: classification for every positive integer step

Let d > 0 and write d = b^2*a, where a is squarefree and b > 0.
For every m, the set {d,2d,...,md} has no nonempty square subset sum
**if and only if m(m+1) < 2a** (`general_step_criterion`).
`all_positive_steps_classified` obtains such a decomposition for every
positive d and supplies the classification uniformly for all m.

For a squarefree step a (including composite a), the condition also
characterizes avoidance of every perfect-power subset sum
(`squarefree_exact_criterion`). Nguyen–Vu Remark 1.3 already notes that
squarefree steps can replace primes in the classical construction.
No mathematical priority is claimed for this extension or classification.

For a general step d, the classification is specifically about **squares**.
The formal counterexample `nonsquare_step_does_not_imply_power_avoidance`
shows that {8} has no square subset sum but does have a cube subset sum.

The earlier prime-step theorems and uniform lower bound are retained.
This extends the construction family, not the upper bound for arbitrary
integer sets in the original problem.

## Mathematical statements

For a prime p and any natural m, let A(p,m) = {p,2p,...,mp}.

1. Every nonempty subset of A(p,m) has a nonsquare sum **if and only if**
   m(m+1) < 2p (`exact_criterion`).
2. The same criterion is equivalent to avoidance of all x^k with x natural
   and k >= 2 (`multiples_power_free_iff`).
3. If the criterion fails, an actual nonempty subset sums to p^2
   (`multiples_square_witness`).
4. For every m, a set of exactly m positive integers in [1,m^2(m+1)]
   avoids all perfect-power subset sums (`exists_power_free_card`).
5. For every N,m with 2m^3 <= N, such an m-element set exists in [1,N]
   (`cubic_lower_bound`). This is a uniform cube-root lower bound.
6. The twelve multiples of 79 from 79 through 948 form a certified example
   in [1,1000] (`example_twelve`). All 4095 nonempty subsets are covered
   by the general proof, without enumeration.

## Argument

Every subset sum has the form pt, where 1 <= t <= m(m+1)/2. If t < p,
then p divides pt but p^2 does not. A perfect power of exponent at least two
which is divisible by the prime p must also be divisible by p^2.

Conversely, the subset sums of {1,...,m} include every integer from zero
through m(m+1)/2; the file proves this by induction. If this total reaches p,
we can choose a subset with coefficient sum p, producing p^2.

For the uniform construction, Bertrand's postulate supplies a prime
T < p <= 2T for T = m(m+1)/2 when m > 0. The largest multiple is at most
mp <= m^2(m+1). The empty case m=0 is handled explicitly.

## Scope, attribution and overlap

The construction is credited to Erdős in Example 1.2 of Nguyen and Vu's *Squares in sumsets*. That paper
provides the context and the substantially deeper upper bound:
https://arxiv.org/abs/0811.1311 (published in 2010).
The mathematical discovery of the original result is not claimed here.

A prior external Lean formalization for Erdős 587 already exists at
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587.lean
Its header credits Nguyen and Vu for the informal result, the Formal Conjectures
authors for statements, and Codex/GPT-5.6 Sol for formalization. The entry file
was inspected to check overlap before preparing this package. No proof code
or dependencies from that repository are imported or copied here.

This package's proof and definitions were independently written with OpenAI
ChatGPT assistance, using Mathlib. Neither mathematical novelty, global first
formalization, nor a new complete solution is asserted. Any recognition would
need to concern the incremental, independently checkable formalization and
must be assessed against existing work. There is no guaranteed award amount.

Proposed contributor placeholder: RECIPIENT-JSP-000476-KZ-A.
Written recipient confirmation and organizer review remain pending.

## Reproduction

Pinned compiler: Lean 4.34.0.
Pinned Mathlib: 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
Other dependencies are pinned in lake-manifest.json.

```sh
lake exe cache get Mathlib.Data.Nat.Squarefree Mathlib.NumberTheory.Bertrand Mathlib.Algebra.BigOperators.Intervals Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings as errors, replays the compiled module
through leanchecker, audits twenty target declarations, checks dependency
revisions, and rejects an intentionally false arithmetic theorem. The second
exports the target dependency closures and checks them with pinned NaNoda,
permitting only propext, Classical.choice and Quot.sound.
See VERIFICATION.md for observed results; commands alone are not test results.

Code license: Apache-2.0. Mathlib retains its original authorship and license.
