# JSP-000254 / Erdős 302: the five-eighths lower bound

This development formalizes Stijn Cambie's known construction and its consequence
that the extremal density cannot converge to one half. It does **not** determine
the optimal density, prove that a limit exists, or settle the full JSP-000254 problem.

For every natural number N, it constructs a subset of {1,...,N} of size
5 floor(N/8) with no three distinct members satisfying 1/a = 1/b + 1/c.
Consequently any maximum-cardinality function f satisfies

    f(N) >= 5 floor(N/8) >= 5N/8 - 5,

and, for every positive epsilon, eventually

    f(N) >= (5/8 - epsilon) N.

In particular f(N)/N does not tend to 1/2. An explicit extremal function is defined
and proved to attain its maximum, so the statement is not conditional on an
uninhabited specification.

## Construction and proof

For N = 8t, use the t odd integers 1,3,...,2t-1 together with all 4t integers
4t+1,...,8t. These disjoint parts contain 5t elements. A putative unit-fraction
equation gives ab+ac=bc and a<b,c. If a is in the upper interval, b,c<=8t<2a,
which contradicts that equation. If a is in the lower part, another lower-part
denominator gives a parity contradiction. If both other denominators are in the
upper interval, b,c>4t>2a again contradict the equation. Use t=floor(N/8) for
arbitrary N, then elementary real inequalities give the asymptotic statement.

## Attribution and statement alignment

- Mathematical construction: **Stijn Cambie**, as recorded in the
  [Erdős problem archive](https://www.erdosproblems.com/302) and the
  [fixed formal-conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/302.lean).
- `NoUnitFractionTriple` and `IsMaxNoTripleCard` follow the Formal Conjectures Authors'
  Apache-2.0 definitions. Their attribution and license are retained.
- New proof scripts: `RECIPIENT-JSP-000254-KZ-A`, submitting account
  `ketianzhang1-lang`, prepared with OpenAI Codex assistance. No original
  mathematical discovery or globally first formalization claim is made.
- `Erdos302.erdos_302.variants.lower_five_eighths` and
  `Erdos302.erdos_302.parts.ii` have the same mathematical statements and definitions
  as the two admitted statements in that fixed upstream snapshot. They are proved
  here without importing the upstream file.
- Public award-repository searches for `JSP-000254` and `302` returned no matching
  entries during preparation on 2026-09-17. This bounded search is not a priority
  guarantee. The reviewed plby snapshot was
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, which had no `Erdos302.lean` file.

## Reproduce

Lean and Mathlib: v4.34.0; exact dependency revisions are in `lake-manifest.json`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as errors, runs Lean's kernel checker,
checks all 12 audited declarations against the axiom allowlist
`propext`, `Classical.choice`, `Quot.sound`, verifies dependency revisions, and checks
that the false arithmetic statement 1=0 is rejected. The second exports the audited
declarations and their dependency closure and checks them using the independently
implemented NaNoda checker at a pinned revision. CI retains the logs, exported
dependency closure, checker configuration, source archive and hashes as an artifact.

No award, claim eligibility, recipient confirmation, independent human review or
payment follows from successful execution. The catalog's full problem remains open.
