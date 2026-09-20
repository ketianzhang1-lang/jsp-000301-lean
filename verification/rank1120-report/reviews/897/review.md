# JSP-000897 — semantic and provenance review

**Pre-execution conclusion: full original scope is established semantically for both explicitly submitted versions; fresh execution remains pending.** A previously missing primary-source comparison is now resolved. The original 1975 forcing threshold is one above the ordinary extremal number; the submitted strict endpoint supplies this exact requirement. Both catalog-selected proof commits must be checked separately.

1. **Original problem correspondence:** yes, against Erdős's original paper, with threshold conventions and strict linear degree handled explicitly.
2. **Exact selected commits actually verified in this batch:** pending isolated checks of both original and stability packages.
3. **Complete original scope:** both packages retain the complete strict and non-strict endpoints; the stability version adds a refinement without replacing any original case.
4. **Lean acceptance completeness:** pending inspection of all execution evidence; no current pass is inferred from older CI.

## Original source recovered and visually checked

Primary source: P. Erdős, *Some recent progress on extremal problems in graph theory*, Congr. Numer. 14 (1975), 3–14, [author archive PDF](https://www.renyi.hu/~p_erdos/1975-42.pdf#page=12), printed page 14 / PDF page 12. The scan itself was inspected on 2026-09-20 because its OCR incorrectly reads the argument of the local threshold as `n` rather than `m`.

In paraphrase: let f_r(n) be the minimum edge count that forces K_r. Does a graph at that threshold have a vertex of degree m>c_r n whose open neighbourhood spans at least f_(r-1)(m) edges? The page identifies r=4 as the first interesting case. In the ordinary extremal-number convention f_r(n)=ex(n,K_r)+1. The proof's strict endpoint therefore covers the original request, while its non-strict endpoint also proves the catalog's threshold wording. Taking c_r=1/4 follows from n≤2m for n≥2. Cases n<2 have no graph at the forcing threshold. This is the complete required range; no equality-case classification is asked.

The current `erdosproblems.com/1079` and `/latex/1079` pages still return 403, but this is no longer a blocker because the original cited publication is available. The old README's source-access limitation is historical and superseded by this review. Keep only source URL, location, paraphrase and hashes in public evidence; do not redistribute the complete paper or page image.

## Fixed versions and live-catalog discrepancy

- [PR #439](https://github.com/TheJustinSunPrize/awards/pull/439), observed head `ed4fc4f546603d21ccf0dfd50a52d65d4db1d8cc`, changes only Lean proof and Attribution basis in one catalog file.
- Original package: repository `ketianzhang1-lang/jsp-000301-lean`, branch `jsp-000897-dense-neighborhood-kz`, commit `914c6fa28200985d6409b5b34588b9f5c4a87d00`, project `projects/jsp-000897`.
- Additional complete package already selected in the catalog but omitted from the old PR body: branch `jsp-000897-degree-stability-20260919`, commit `4d15dc035f56658776c01729216f99b776a5ad35`, same project. The replacement body explicitly lists both; the supplement is not silently dropped.
- `verify_supplement.py` compares every retained original Lean source, toolchain, lakefile and manifest to commit `914c6...` and aborts on any byte change. It needs that historical Git object available.
- Original credited upstream: `plby/lean-proofs` commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, file `src/latest/ErdosProblems/Erdos1079.lean`; original retained at `upstream/Erdos1079.lean`, SHA256 `09efec8509c86a61575eed184fd68d76d09a4f74ca94b7338478cb5657f9cae3`.

## Scope matrix

| Requirement or claimed supplement | Original selected proof | Independent audit bridge |
|---|---|---|
| Ordinary finite simple undirected graphs, genuine undirected edge count, open neighbourhood | `edgeCount = Nat.card G.edgeSet`; `linkEdgeCount` counts `Sym2` edges all of whose endpoints are adjacent to v | Literal Mathlib graph, edge-set, adjacency and cardinality expressions in all bridges. |
| All r≥4, n≥2, ordinary non-strict threshold; maximum-degree witness and n≤2d | `Erdos1079.erdos_problem_1079`, `JSP000897.resolution_with_surplus` | `catalog_threshold`. |
| Original forcing threshold ex+1 globally and locally | `Erdos1079.erdos_1079`, `JSP000897.strict_resolution` | `forcing_threshold` separately changes the natural strict inequalities to explicit +1 bounds. |
| A positive c_r and strict d>c_r*n | Same full endpoints | `uniform_linear_constant` supplies real c=1/4 uniformly for every r≥4. |
| Every certified surplus at every maximum-degree vertex | `surplus_at_every_maximum`, `surplus_dominates` | `every_maximum_surplus`; original axiom audits also cover the exact existence endpoint. |
| Stability package: any r≥3, deficit δ, surplus s, chosen v with maxDegree≤d+δ | `surplus_with_degree_deficit` and six related theorems | `degree_deficit`, `every_maximum_from_three`; no assumption that arbitrary vertices are maximal. |
| Preserve original complete endpoint in stability package | `complete_with_stability` combines original resolution and all approximate maxima | Fifteen original targets and all four original-source bridges retained, plus two supplement bridges. |

The ordinary extremal number uses Mathlib's actual maximum over clique-free graphs. Edges are unordered pairs counted once; the neighbourhood is open, so its center is excluded. The finite vertex type `Fin n` represents every n-vertex simple graph up to labeling and does not restrict graphs to a constructed family. All inequalities use natural arithmetic with explicit n≥2 where a linear-degree conclusion is required. The chosen c=1/4 is deliberately strictly below the established one-half lower bound. Stability allows any n with an actual vertex v; the deficit penalty δ(n−d) is an upper loss estimate, not a claimed optimum. The triangle extension r=3 is additional, not a narrowing of the original r≥4 theorem.

## Actual-check plan

Both selected commits use Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; all nine package revisions are pinned. Base `verify.sh` clean-builds the two mathematical modules, replays both, audits eight declarations, checks actual dependency revisions and rejects false arithmetic. The new base manifest has 12 entries (8+4).

The stability verifier repeats all original checks, strict-compiles and replays `JSP000897Stability`, checks all 15 original declarations, preserves byte hashes and rejects its own false arithmetic control. Its fresh manifest has 21 entries (15+6). The exact selected lakefile does not register the flat Stability module as a native Lake target: explicit compilation is the original verifier's intended mechanism. The official target audit must use an openly documented narrowly scoped equivalent build for that module, with exact command/source/output hashes and all normal calls delegated to the real pinned Lake. No modified proof or lakefile is treated as the selected source. All bridge declarations are placed under the existing configured `JSP000897` library.

The unmodified official audit is supplemented by strict bridge prechecks, replay and NaNoda checks of all target closures. The selected mathematics contains no `sorry`, added axiom, native computation trust extension or kernel bypass. Final conclusions require actual logs, negative controls, stable inputs and standard-only transitive axiom closures; source scanning alone is insufficient.

## Credits, licenses and award boundary

The retained upstream file credits Codex and GPT-5.6 Sol as formal authors, and Bollobás/Thomason for the mathematical argument, with Bondy's strict strengthening. Its original Apache-2.0 header and full license are retained, and the port is labeled modified. The root repository's separate MIT license does not replace this project's Apache-2.0 notice.

The applicant's own work consists of the Lean 4.34 compatibility port, four surplus supplement theorems, seven degree-deficit/triangle-threshold supplement theorems, integration and reproducible verification, with OpenAI ChatGPT/Codex assistance. The stability source explicitly states that edge charging and Turán splitting adapt the credited development. Do not imply an independently invented mathematical proof, claim the upstream source as the applicant's, or infer award entitlement from successful verification. Existing overlaps #24, #1333, #1187, #155 and #736 remain disclosed. Their separate results are not certified here.

The PR and claim are still pending. Mathematical review and solver registration must precede official Lean registration. The original before-opening self-check timing cannot be recreated; that checkbox stays unchecked. The claim's merged-PR declaration also stays unchecked, and its repository is a proposed formalization source while the catalog amendment is pending.
