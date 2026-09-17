# JSP-000746: integer-graph resolution and the exact finite threshold

We provide the original integer-graph conclusion together with the exact finite threshold. Every triangle-free simple graph on the integers contains three distinct, pairwise nonadjacent vertices a, b, a+b. Our integer endpoint finds positive witnesses already among labels 1,...,18.

## Our formalization contribution

Our contribution, recorded under GitHub account `ketianzhang1-lang` and developed with OpenAI ChatGPT assistance, comprises:

1. An explicit 43-edge graph on 17 vertices, checked in Lean to be triangle-free and to have no independent distinct-summand Schur triple.
2. A restriction argument giving counterexamples at every order from zero through seventeen.
3. The exact-threshold equivalence: the finite forcing property holds if and only if n >= 18.
4. An explicit embedding of labels 1,...,18 into the integers, transport of the finite theorem, and a separately named endpoint with all three distinctness conditions.
5. A pinned Lean 4.34 project, exact theorem-type checks, axiom audits, kernel replay and a negative control.

The upper-bound certificate and its substantive formal proof are an attributed dependency. [PROVENANCE.md](PROVENANCE.md) identifies the source and the import-only compatibility change.

## Complete original endpoint

`JSP000746.jsp_000746` in [JSP000746.lean](JSP000746.lean) proves, for every `G : SimpleGraph ℤ` with `G.CliqueFree 3`, that there exist integers a, b, c satisfying

```text
a != b, a != c, b != c, c = a+b,
not G.Adj a b, not G.Adj a c, not G.Adj b c.
```

The supporting theorem `JSP000746.integer_graph` additionally gives 0 < a < b and a+b <= 18. Thus the distinctness and sum condition use actual integers. The proof places no finiteness condition on G and introduces no additional unproved assumption.

`JSP000746Sharp.exact_threshold` and `JSP000746Sharp.least_threshold` in [JSP000746Sharp.lean](JSP000746Sharp.lean) retain the sharp finite result. The separate stronger Hindman-set question is outside the JSP-000746 catalog's stated integer-triple question.

## Source and reproduction

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000746-sharp-kz`
- Project: `projects/jsp-000746-sharp`
- Lean: 4.34.0
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`; all transitive revisions are in `lake-manifest.json`.

Check out the exact full commit selected in [PR #402](https://github.com/TheJustinSunPrize/awards/pull/402), enter the project directory, and run:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib.Tactic Mathlib.Combinatorics.SimpleGraph.Clique Mathlib.Tactic.Sat.FromLRAT
bash scripts/verify.sh
```

Keep the committed dependency manifest. Bootstrap checks every upstream source and certificate hash before applying the recorded import-only change. The verification script compiles every proof module with warnings treated as errors, replays all three modules, checks the exact integer statement and eight axiom closures, checks dependency revisions and rejects an invalid arithmetic statement. Certificate reconstruction requires substantial memory; the public workflow provides swap and a 14 GB Lean cap.

The previous Python witness and LRAT checkers remain in `evidence/jsp-000746-sharp/` at repository root. Their historical receipt is separate from the verification of the new integer endpoint. See [VERIFICATION.md](VERIFICATION.md) for the current execution record.

## Requested review

We request formalization credit for the concrete additions above. Mathematical credit for the upper bound remains with Ben Barber; the reused formal proof retains its original attribution. The complete statement, source correspondence and contribution eligibility are submitted for organizer review. Contributor-run checks do not establish first-formalization priority or an award decision.
