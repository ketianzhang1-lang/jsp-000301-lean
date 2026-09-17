# Statement alignment and non-vacuity

Official entry: [JSP-000057](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000057).
It asks for an exponential bound in the uniform set size, for each fixed
number of petals. This project covers only uniform size **2** and petal
count **3**. The word "complete" would apply only to this scoped case.

Formal Conjectures source, pinned at
[`40e7c98697de6f66b8cbdbf641749ab39ed9c152`](https://github.com/google-deepmind/formal-conjectures/tree/40e7c98697de6f66b8cbdbf641749ab39ed9c152):

- [Threshold definition](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/20.lean)
- [Sunflower definitions](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean)

The three definitions are reproduced with explicit placement of the implicit
ground-type binder and a local bound-variable rename. The predicates are the
same; no research theorem with an unfinished proof is imported.

| Requirement | Formal treatment |
| --- | --- |
| Distinct members | Families are sets, or finite sets, so duplicates cannot count. |
| Uniformity | Every member has cardinality exactly 2. |
| Petal count | The chosen subfamily has cardinality exactly 3. |
| Kernel | Every pair of distinct petals has the same intersection; empty kernel is allowed. |
| Ground set | The threshold ranges over every `α : Type`, as in the original definition. |
| At least the threshold | `m <= F.ncard`; no exact-size substitution. |
| Sharpness | The six edges `{0,1}`, `{0,2}`, `{1,2}`, `{3,4}`, `{3,5}`, `{4,5}` defeat every `m <= 6`. |
| Infimum | `original_threshold_iff` identifies the defining set exactly as `{m | 7 <= m}`. |

`Set.ncard` is zero for infinite sets. Consequently `7 <= F.ncard` implies
that the family is finite, and the two-element assumption implies each
member is finite. The code proves these facts before conversion to finite
sets. It does not silently reinterpret infinite cardinalities.
For the necessity direction, a finite six-member witness refutes the
threshold predicate for every smaller natural number, including zero.
`f_two_three` therefore does not exploit the empty-infimum convention.

`Audit.lean` checks both the numerical equation and the fully expanded
original threshold predicate, so the result is stronger than an isolated
calculation of an infimum.
