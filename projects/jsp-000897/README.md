# JSP-000897: complete classical threshold theorem and an integral-surplus supplement

We provide the complete dense-neighbourhood threshold theorem together with an explicit integral-surplus refinement at every maximum-degree vertex. Our contribution, recorded under GitHub account `ketianzhang1-lang`, comprises the Lean 4.34 port, the surplus-preservation and surplus-difference theorems, the complete existence endpoint and the strict-threshold corollary, with a pinned verification package. We developed these additions with OpenAI ChatGPT/Codex assistance.

The classical threshold proof is an attributed dependency. [PROVENANCE.md](PROVENANCE.md) and the retained source headers identify the upstream mathematical and formalization contributions.

Let ex(n,K_r) be the ordinary extremal number, e(G) the number of edges, d(v) the degree, and e(N(v)) the number of edges with both endpoints in the open neighbourhood of v. For every r >= 4, n >= 2 and simple graph G on n vertices with e(G) >= ex(n,K_r), the main theorem produces a maximum-degree vertex v with

- n <= 2*d(v);
- ex(d(v),K_(r-1)) + (e(G)-ex(n,K_r)) <= e(N(v)).

In particular, the complete non-strict threshold conclusion holds, and a strict global surplus gives the strict local conclusion. `surplus_at_every_maximum` proves the corresponding inequality for every maximum-degree vertex and any certified natural-number surplus s. The definitions count genuine undirected edges, not ordered adjacent pairs; the neighbourhood is open.

## Proof structure

1. At a maximum-degree vertex of degree d, every edge outside the neighbourhood can be charged to an endpoint outside it. Thus e(G) <= e(N(v)) + d*(n-d).
2. Join the (r-2)-partite Turan graph on d vertices to an independent set of size n-d. Its K_r-freeness and Turan's theorem give ex(d,K_(r-1)) + d*(n-d) <= ex(n,K_r).
3. Subtract the common cross term. Any integral surplus in the global inequality remains in the neighbourhood.
4. The balanced complete bipartite graph and the handshake identity give n <= 2*d(v) for n >= 2.

## Source and statement correspondence

Catalog: https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000897

Related problem: https://www.erdosproblems.com/1079 . The public problem page returned HTTP 403 during this preparation; exact formal quantifiers were checked against the immutable credited source and the catalog description, not a newly retrieved problem-page transcript. Final source-statement adjudication remains with reviewers.

The full existing endpoints are `Erdos1079.erdos_problem_1079` and `Erdos1079.erdos_1079`. The new main endpoint is `JSP000897.resolution_with_surplus`. The n >= 2 boundary is explicit because a one-vertex graph cannot have degree at least n/2. The original large-n question is covered by this range.

## Pinned proof and verification

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000897-dense-neighborhood-kz`
- Verified proof commit: `914c6fa28200985d6409b5b34588b9f5c4a87d00`
- Project: `projects/jsp-000897`
- [Successful verification run 35178602861](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178602861): build, both module replays, eight axiom audits, dependency checks and negative control passed; NaNoda checked 11,259 declarations without errors.

The complete main endpoint is `JSP000897.resolution_with_surplus` in [JSP000897.lean](JSP000897.lean). The underlying threshold endpoints are in [Erdos1079.lean](Erdos1079.lean).

## Reproduce

Check out the exact proof commit above and enter `projects/jsp-000897`.

Lean v4.34.0; Mathlib v4.34.0 at `5ed2965256430c3649e86755f9576b54eca72435`. All transitive package revisions are pinned in lake-manifest.json.

```bash
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Extremal.Turan Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

See [VERIFICATION.md](VERIFICATION.md) for actual results and their limits.

## Requested review

We submit our port, surplus formalization and verification contribution through [awards PR #439](https://github.com/TheJustinSunPrize/awards/pull/439). The complete main theorem is included; our requested contribution credit concerns the specific additions described above. The checked proof files, locked dependencies and scripts are unchanged by this documentation follow-up. Contributor-run verification supports review; acceptance, attribution and eligibility remain organizer decisions.
