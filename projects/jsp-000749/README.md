# JSP-000749 / Erdos 901: classical upper-bound component

For every natural n >= 2, this project proves `0 < m(n) <= 4*n^2*2^n`, where m(n) is the least edge count of a finite simple n-uniform hypergraph of weak chromatic number exactly three. The minimum is proved nonempty and attained. The stronger existence theorem supplies such a hypergraph on `Fin (2*n^2)`, with every proper edge subfamily two-colourable. Isolated vertices are allowed; vertex-criticality is not asserted.

**Scope:** this is a complete formalization of a known all-parameter upper bound, not a solution of the full precise-growth problem, not an improved bound, and not an optimal constant. No award or global first-formalization priority is asserted.

## Proof and semantics

`JSP000749.jsp000749_upper_bound` is the universal existence theorem. `m_attained`, `m_positive` and `m_upper_bound` establish the extremal-function statements. `StatementCheck.lean` restates existence with ordinary finite sets, cardinality and explicit functions into Fin 2 and Fin 3, rather than assuming the meanings of custom predicates. It is contributor-written, not an independent human attestation.

Take N=2*n^2 vertices and E=choose(N,n) candidate edges. Every two-colouring has at least D=choose(n^2,n) monochromatic edges. An elementary falling-factorial product estimate proves E<=2^(n+1)*D. Put a=2^(n+1), M=N*a. An injection of hypothetically failing tuples into a dependent sum of bad-tuple spaces would imply E^M<=2^N*(E-D)^M. With q=1-D/E, `1-x<=exp(-x)` and `2<exp(1)` prove `(2*q^a)^N<1`, contradicting that count. A hitting tuple therefore exists. Its finite image removes duplicate edges without destroying the obstruction.

An inclusion-minimal non-two-colourable edge subfamily is exactly three-colourable: delete one edge, two-colour the rest, then give one vertex of that edge the third colour. The n>=2 condition ensures every edge containing that vertex has another vertex of an old colour. All other edges retain their original proper colouring. No random simulation or external solver result is a proof dependency.

## Reproduction

Lean 4.34.0 and all nine resolved dependencies are pinned. From this directory:

```sh
sha256sum -c SOURCE_SHA256SUMS
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The source manifest checks fifteen proof, audit, configuration, script and license files. These bytes match the previously delivered local proof package. Documentation is deliberately outside the source manifest; it is versioned by the Git commit. Prior local logs remain in the contributor's original delivery package and are not relabeled as public CI. The fresh public workflow is `.github/workflows/jsp-000749.yml`; inspect its actual result before claiming success. It checks six modules, twelve target axiom closures and negative/finite controls, then runs pinned NaNoda on all target closures. At publication of this initial commit, public CI and NaNoda are pending. Successful contributor-run checks do not constitute organizer approval or independent human certification. Cached dependencies and network access are used; an offline from-source rebuild of all Mathlib is not claimed.

## Attribution and prior work

Mathematical credit remains with Paul Erdos and the cited literature. This independent Lean implementation was prepared with OpenAI ChatGPT assistance under the submitting account's direction. Mathlib contributors retain all infrastructure credit. The constant 4 is a conservative explicit instance of the classical asymptotic bound.

- P. Erdos, *On a combinatorial problem. II* (1964): https://doi.org/10.1007/BF01897152
- Duraj, Kozik, Shabanov, *Random hypergraphs and property B*: https://arxiv.org/abs/2102.12968
- Problem: https://www.erdosproblems.com/901
- Catalog: https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000749
- Acknowledged incomplete prior attempt: https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos901Problem.lean . Its main upper-bound statement contained `sorry` when inspected; it is not imported or redistributed and its assertions are not assumed.

Bounded prior searches did not identify a matching completed upper-bound proof; public indexing is incomplete and this is not a priority certificate. Proposed recipient placeholder: `RECIPIENT-JSP-000749-KZ-A`, confirmation pending. Eligibility for the exact known-result component, priority, official verification and any award remain for the organizers. No private identity/payment details, curator signatures, existing catalog flags or award records are supplied or changed.
