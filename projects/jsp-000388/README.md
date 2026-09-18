# JSP-000388: our quadratic obstruction and complete polynomial-tiling endpoint

We provide a complete Lean endpoint for the original existence question:
there is an integer polynomial of degree at least two whose integer value set
has an additive complement giving each integer exactly one representation.
The witness polynomial is **X⁶**. We combine the attributed, complete
sixth-power tiling proof with our separately implemented quadratic obstruction,
and prove a general translation law and its shifted-polynomial consequences.

## Our contributions

We developed our implementation and integration under GitHub account
`ketianzhang1-lang` with OpenAI ChatGPT/Codex assistance.

- Our original module proves the obstruction for every polynomial
  `a*x²+b*x+c` with `a ≠ 0` and `a ∣ b`, including b=0 and either sign of a.
  Its source is unchanged from the previously verified revision.
- We identify our exact-complement predicate with the imported tiling predicate.
- We prove a general translation law: adding c to the value set translates the
  complement by −c. Hence every polynomial `X⁶+C(c)` has an exact complement,
  uniformly for every integer c.
- We supply an endpoint matching the original polynomial-degree and
  pair-value-uniqueness formulation, together with a combined existence and
  quadratic-obstruction theorem.
- We pin the full upstream proof chain, verify original and compatibility-port
  hashes, and supply a Lean 4.34 reproduction and verification package.

## Complete original statement

`JSP000388.jsp_000388` in [JSP000388Complete.lean](JSP000388Complete.lean) proves:

```text
∃ f : Polynomial ℤ, 2 ≤ f.degree ∧ ∃ A : Set ℤ,
  ∀ z : ℤ, ∃! p ∈ A ×ˢ Set.range f.eval, z = p.1 + p.2
```

Uniqueness concerns the two **summand values**, not the input of the polynomial.
No finite restriction is imposed on the integers or the complement set. The
original question is existential, so the single polynomial X⁶ suffices.
We do not claim a classification of all possible degrees, an answer for X³,
or a new proof that every even exponent at least six works.
See [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md) for the exact comparison.

## Attribution and source dependency

The affirmative proof is reused from **plby/lean-proofs**, branch `main`,
commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, entry
`src/latest/ErdosProblems/Erdos477.lean`. Its formal author is **Codex**.
Its source credits Liam Price (GPT 5.6 Sol Pro), *Large Powers Tile the Integers*,
and the earlier general greedy criterion from Pengbinghui/pipeline-math.
Original source headers and license notices are retained.

The mathematical square and quadratic obstructions are credited to Milan
Sekanina, AlphaProof and Sarosh Adenwalla as documented in our original source
record. We request assessment of our separately implemented obstruction,
translation theorem, interfaces and verification integration. We do not claim
new mathematics, an independently developed sixth-power proof or first
formalization of the original problem. Earlier competing quadratic submission
[PR #61](https://github.com/TheJustinSunPrize/awards/pull/61) is acknowledged.

[PROVENANCE.md](PROVENANCE.md) records our contributions and dependency lineage.
[UPSTREAM.json](UPSTREAM.json) fixes every imported source, checksum and
mechanical compatibility change. Imported proof files are downloaded from
immutable URLs by the bootstrap script. The finite-avoidance, determinant,
geometry and counting steps are proved in that chain, not assumed as axioms.

## Reproduction

Lean is pinned to **4.34.0**, Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`, and all nine dependency revisions are
locked in `lake-manifest.json`. From `projects/jsp-000388` at the selected commit:

```sh
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
python3 scripts/verify_complete.py
```

Keep the committed dependency manifest. Network access and pinned cached
Mathlib objects are used. The verifier compiles the complete local proof chain
with warnings as errors, audits 18 theorem closures, replays the upstream and
our proof modules with Lean's kernel, checks every dependency revision and
requires a false-arithmetic control to be rejected.

Actual checks and their limits are recorded in [VERIFICATION.md](VERIFICATION.md).
The optional separately implemented checker can be run with
`bash scripts/verify_nanoda.sh`; a configured check is not a successful result.
The workflow exposes the status of hosted reproduction for each proof commit.

The awards PR contains catalog text and references only; sources and build
materials remain in this repository. Maintainer review, contribution eligibility,
priority and any award decision remain pending.
