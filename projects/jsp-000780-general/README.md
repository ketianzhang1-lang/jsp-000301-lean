# JSP-000780 / Erdős 939: explicit families for every r ≥ 6

This package extends the author's earlier r=6 implementation to **every integer
r ≥ 6**. For each such r it constructs infinitely many sets of exactly r−2
distinct positive r-full integers, with collective gcd 1 and an r-full sum.
Their sums are distinct as well. An integer is r-full when every prime divisor
occurs to exponent at least r.

**Attribution and scope:** this formalizes a known binomial construction,
attributed in the pinned source to GPT-5.5 Pro prompted by Liam Price.
A prior Aristotle formalization covering r ≥ 6 is reported in PR #65's
prior-art assessment. No first-formalization or new mathematical discovery
claim is made. This does not settle r=4, r=5 infinitude, or the whole catalogue
entry. See [PROVENANCE.md](PROVENANCE.md).

The parameter is an explicit arithmetic progression; it need not be prime.
All definitions are executable. The modulus is a product of coefficients,
not a factorial. See [PROOF.md](PROOF.md) for the construction and argument.

## Main declarations

All are in namespace `JSP000780General`.

- `solution_for_every_parameter`: every natural parameter gives a valid set.
- `infinitely_many_solutions`: infinitely many sets for every r ≥ 6.
- `infinitely_many_totals`: infinitely many sums for every r ≥ 6.
- `original_all_r_infinite`: the result with the source's prime-factor predicate.
- `original_every_parameter`: the constructive result in the same predicate.

`OriginalSolutions` reproduces the source's defining conditions using
`Finset.gcd id = 1` for collective coprimality. It does not require pairwise
coprimality. The source's unfinished conjectures are not imported.

## Reproduce

Install Elan and the toolchain in `lean-toolchain`, then run:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The manifest pins Mathlib and its eight dependencies. `verify.sh` compiles,
replays the Lean kernel, checks target axiom lists and dependency revisions.
The second script independently checks exported proof terms using NaNoda.
See [VERIFICATION.md](VERIFICATION.md) for checks actually completed, which
must be distinguished from merely supplied reproduction commands.

The supplementary materials relate to existing award PR #370. They do not
constitute organizer approval or a payment entitlement.
