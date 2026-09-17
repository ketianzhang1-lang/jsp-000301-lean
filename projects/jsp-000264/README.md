# JSP-000264 / Erdős 318: a positive-density counterexample

This project proves the complete positive-density existence part (part i) of
Erdős Problem 318: a set of positive natural density need not have property P₁.
The explicit set is all positive odd integers together with 2. Its natural
density is exactly 1/2. This is a formalization of a known result, not a new
mathematical discovery.

**Partial scope relative to the entire catalog entry.** The proof does not
establish P₁ for all natural numbers, all odd numbers, all infinite arithmetic
progressions, or the squares with 1 removed. In particular it does not prove
the separate Larsen squares-without-1 result (part ii).

## Proof

Give 2 the sign +1 and each odd element the sign -1. Both signs occur on the
set. A finite nonempty subset omitting 2 has a strictly negative reciprocal
sum. A subset containing 2 could have sum zero only if a finite sum of odd
reciprocals equalled 1/2. Induction writes that sum as p/q with p,q natural and
q positive and odd. Equality would imply q = 2p, a contradiction.

Below N, for every N >= 3, the set contains exactly floor(N/2)+1 elements.
Dividing by N and applying the squeeze theorem gives the genuine natural
density 1/2, not just a positive lower-density estimate.

## Checked targets

In namespace `JSP000264`, `counterexample_not_P₁` proves the obstruction,
`counterexample_count` proves the exact counting formula,
`counterexample_density` proves the limit, and
`positive_density_counterexample` combines them into the existence theorem.
`source_statement_positive_density` gives the endpoint using the reference's
unsimplified density expression.
`odd_denominator` is the arithmetic lemma used by the proof.

The formalization uses real-valued signs, nonconstancy on the nonzero members,
arbitrary nonempty finite subsets, and real reciprocal sums. See
[STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md) for the original-statement mapping
and [PROVENANCE.md](PROVENANCE.md) for credit.

## Reproduction

Lean `leanprover/lean4:v4.34.0` and the committed Mathlib manifest are required.
Keep the manifest unchanged; do not run `lake update` for reproduction.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The submission receipt identifies the exact passing source commit and run.
Build success alone is not an award or an organizer's verification decision.
