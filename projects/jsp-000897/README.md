# JSP-000897: complete classical threshold theorem and an integral-surplus supplement

This package reproduces and ports the existing complete Lean resolution of the dense-neighbourhood problem, then exposes its integral surplus at every maximum-degree vertex. Original mathematical and formalization credits are retained in [PROVENANCE.md](PROVENANCE.md).

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

## Reproduce

Lean v4.34.0; Mathlib v4.34.0 at `5ed2965256430c3649e86755f9576b54eca72435`. All transitive package revisions are pinned in lake-manifest.json.

```bash
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Extremal.Turan Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

See [VERIFICATION.md](VERIFICATION.md) for actual results and their limits.

## Requested assessment

This is a self-submission of the port, incremental formalization and reproducibility evidence only. A complete earlier formalization already exists. It is not a claim to the original solver credit, first-formalizer priority, independent human verification, an approved award or payment entitlement. Please assess whether these incremental contributions qualify for recognition.

Proposed placeholder: RECIPIENT-JSP-000897-KZ-A. Confirmation pending. No public written-confirmation attestation is supplied. Catalog eligibility is currently No; this package does not change that flag or create a candidate/award record.
