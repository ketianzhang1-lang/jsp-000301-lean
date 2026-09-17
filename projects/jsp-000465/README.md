# JSP-000465: full compactness counterexample interface and uniform separation

We provide a complete Lean endpoint disproving the proposed reduction from a forbidden family to a single forbidden member. Our development retains a counterexample consisting entirely of **connected bipartite graphs containing cycles**, and proves a simultaneous strict separation for every positive comparison constant.

## Our formalization contribution

Our contribution, recorded under GitHub account `ketianzhang1-lang`, comprises the Lean 4.34 compatibility port, the dedicated problem interface and the following supporting results, developed with OpenAI ChatGPT/Codex assistance:

1. `JSP000465.familyExtremal_singleton` identifies the family extremal number with Mathlib's ordinary single-graph extremal number for singleton families.
2. `JSP000465.familyExtremal_attained` supplies an actual family-free graph attaining the extremum.
3. `JSP000465.uniform_separation` and `JSP000465.connected_bipartite_counterexample` establish a uniform eventual strict comparison for every member of one fixed nonempty finite forbidden family.
4. `JSP000465.not_bipartite_compactness` directly negates the universal compactness assertion.
5. We supply locked dependencies, exact theorem audits, kernel replay, a negative control and NaNoda verification.

The substantive quantitative counterexample is imported from the credited upstream proof. [PROVENANCE.md](PROVENANCE.md), the retained source headers and license notices distinguish that work from our additions.

## Full statement

There exists a fixed nonempty finite family F of connected bipartite finite simple graphs, each containing a cycle, such that for every real K > 0, for all sufficiently large natural n, simultaneously for every H in F,

```text
K * ex(n,F) < ex(n,H).
```

The extrema use ordinary subgraph containment. The threshold is eventual over every natural host order, with all members handled simultaneously. Finite graphs on `Fin n` represent all finite simple graphs up to relabelling. The complete original negative answer is `JSP000465.not_bipartite_compactness` in [JSP000465.lean](JSP000465.lean); the strengthened endpoint is `JSP000465.connected_bipartite_counterexample`. See [STATEMENT_REVIEW.md](STATEMENT_REVIEW.md).

## Pinned proof and verification

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000465-verified-kz`
- Verified proof commit: `6a793b157c1afdf29f3e6bbbf3cf514535d1dfca`
- Project: `projects/jsp-000465`
- [Successful verification run 35178564666](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178564666).

The warning-as-error build, all eight module replays, seven axiom audits, dependency checks and negative control passed. NaNoda checked 42,570 declarations without errors. The audited axiom closures are restricted to `propext`, `Classical.choice` and `Quot.sound`. [VERIFICATION.md](VERIFICATION.md) records the execution and retained evidence.

## Reproduce

Check out the exact proof commit above and enter `projects/jsp-000465`. Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` are pinned, including transitive dependencies.

```bash
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Keep the committed dependency manifest. This documentation update leaves the verified Lean files, dependency pins and scripts unchanged.

## Requested review

We submit these formalization contributions through [awards PR #442](https://github.com/TheJustinSunPrize/awards/pull/442), with catalog references to this proof repository. We request review of the complete theorem, attribution and our port, interface and verification contribution. The original mathematical and upstream formalization credit is retained. Contributor-run verification does not decide prize eligibility.
