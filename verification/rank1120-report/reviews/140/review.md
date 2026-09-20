# JSP-000140 / Erdős 136 — semantic and source review

Preparation-stage conclusion: **证据不足 / execution not yet completed**. Static review finds a full asymptotic statement at `724a733a2b498d7b3b956e66b76d7334cc906eaf`, with a genuine unordered-edge minimum and actual eventual colouring witnesses. This batch's exact-version execution remains required. This historical preparation memo must not be mistaken for the final execution judgment.

| Required judgment | Preparation-stage answer |
| --- | --- |
| Is the proof object the original problem? | Yes: the minimum palette for edge colourings of Kn with at least five colours on every K4, and its asymptotic coefficient. |
| Has this batch actually verified the selected commit? | Not yet; inspect the final exact-version execution receipt. |
| Does the formal endpoint cover the entire original question? | Yes at the statement/proof-structure level: the full ratio limit and actual colourings for every sufficiently large n, with no extra upper-construction hypothesis. |
| Does it satisfy the requested Lean completeness review? | Temporarily unconfirmed until all fresh checks finish. Formal completeness does not establish prize entitlement. |

## Original source and selected proof

- Primary paper: [Bennett, Cushman, Dudek and Prałat, arXiv:2207.02920v1](https://arxiv.org/abs/2207.02920v1). The [paper PDF](https://arxiv.org/pdf/2207.02920) defines the minimum palette in Definition 1 on page 1, states the full asymptotic in Theorem 1 on page 2, and recalls the classical lower bound in Theorem 2 on page 4. The definition and relevant theorem text were inspected directly. The problem concerns all sufficiently large integer sizes, not just a subsequence or selected small examples.
- Alternative construction source: [Joos–Mubayi, arXiv:2208.12563](https://arxiv.org/abs/2208.12563), whose conflict-free matching approach is used by the imported formal development.
- Own repository and branch: `ketianzhang1-lang/jsp-000301-lean`, `jsp-000140-coloring-kz`, commit `724a733a2b498d7b3b956e66b76d7334cc906eaf`, project `projects/jsp-000140`.
- Own statement/proof endpoint: [`JSP000140.jsp_000140`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/724a733a2b498d7b3b956e66b76d7334cc906eaf/projects/jsp-000140/JSP000140Complete.lean).
- Attributed full upstream proof: [`Erdos136.erdos_136`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean), with [Definitions.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136/Definitions.lean) defining actual unordered edges and an attained least palette. Both were read at the fixed revision.

## Definitions, quantifiers and boundaries

The original pair model is a total function `Fin n → Fin n → Fin k`, symmetric in its arguments. Its admissibility condition requires six unordered off-diagonal edges among every four distinct vertices to use at least five distinct colours. The six-entry `Finset` removes duplicate colours and counts distinct palette values. No proper-colouring assumption is imposed on adjacent edges; such an assumption would strengthen the problem incorrectly.

`JSP000140Bridge` explicitly enumerates all six genuine edges of K4, constructs the two conversions, and proves admissibility in both directions. The backward conversion needs a diagonal palette value. Existence of an actual edge guarantees a nonempty palette when n≥2. Accordingly `pairColorable_iff` and `minPalette_eq` correctly require n≥2. At n=1, the standard edge model has no edge while the pair model still has a diagonal input, so asserting equality without that restriction would be false. The finite exceptional sizes do not change the asymptotic result. At n=0 the definitions remain total; no division-by-zero inference is used because eventual arguments restrict to positive n.

The minimum is attained by `Nat.find`, with both an existence witness and a leastness theorem; it is not an arbitrary bound selected to have the desired asymptotics. The final statements give the normalized limit 5/6, asymptotic equivalence, and for each real epsilon>0 actual colourings for all sufficiently large n using fewer than `(5/6+epsilon)n` colours. For n≥4 the independently implemented finite lower proof gives `5(n−1)<6f(n,4,5)` and the rounded integer bound. No exact all-n formula or explicit onset is claimed.

## Independent audit specification

The auditor-owned `Verify140.Colorable` expands the standard edge-colouring condition over every embedding `Fin 4 ↪ Fin n`. Its own `minimum` is the least natural palette admitting this property. Nine bridge targets check:

- Exact predicate equivalence and existence of a finite palette.
- Equality with the upstream standard minimum, attainment and leastness.
- Equality to the pair minimum only for n≥2.
- The original normalized limit through all natural sizes.
- The strict finite lower bound for every n≥4.
- Genuine unordered-edge colouring witnesses for every positive epsilon and every sufficiently large n.

All 46 original `AuditComplete.lean` targets are included as well, giving **55 audited target entries**. Two upstream endpoints use tracked `AuditComplete.lean` as the verification entry, with separate actual definition paths and ported SHA-256. All own modules are explicitly registered as Lake roots in the selected lakefile, including `JSP000140Bridge`.

## Full closure, fresh execution and trust

The original verifier checks exactly 24 source modules: 20 upstream sources, three own proof modules and AuditComplete. It rejects an unpinned ErdosProblems import or an unexpected closure size. Run without `--resume`, with a removed project build; it compiles every module using warning-as-error Lean, audits 46 closures, replays the ErdosProblems environment and each of the three own proof modules, rejects false arithmetic, checks all nine actual dependency revisions, and verifies source hashes remain stable.

Lean is pinned to 4.34.0, Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`. Every upstream input has original Git-blob and SHA-256 pins, recorded compatibility changes and a resulting SHA-256. Six of the 20 inputs have compatibility changes. The complete conflict-free matching and eventual-construction results are proved in that closure; they are not extra assumptions to the final theorem. `BernoulliFreedman` and `Pippenger` are not imported dependencies of this selected endpoint.

The shared runner must freshly check all 55 targets with the official audit, recheck the independent bridge with the kernel, and export all target closures for the separate NaNoda implementation. Expected standard possible axioms are `propext`, `Classical.choice`, `Quot.sound`; actual target results must be reported from fresh logs. Source inspection is not a substitute for those results. Exporter compatibility rebuilding and contributor-operated trust boundaries must be disclosed by the final common report.

## Authorship and licensing

Direct source comparison confirms the original own module is byte-identical to `b9c7f4e9dfe6b9f398533b02c4b93805e1abc8f1`, SHA-256 `e41cf87887310cfbc9a1c83e70e090ddc790e35e6c504b16599b39360180060d`. It has 22 public lower-bound declarations; the bridge and endpoint add 22 further public declarations. The upstream full asymptotic theorem already includes a classical lower argument: our original strict lower theorem is an additional conclusion, not the source of the imported complete asymptotic proof.

The applicant identifies the separately implemented lower development, exact model bridge, attained-minimum transport and integration, with OpenAI ChatGPT/Codex assistance. Mathematical credit remains with Erdős–Gyárfás, Erdős–Elekes–Füredi, Bennett–Cushman–Dudek–Prałat and the cited Joos–Mubayi construction. The imported source credits Codex and GPT-5.6 Sol and retains OpenAI Codex copyright notices and Apache 2.0 licensing. The full Apache license and upstream license notice are present in the selected project. Preserve these with all redistributed source copies and retain compatibility-change notices. No imported authorship, independent reimplementation of the complete upper proof, first-formalization priority, or new mathematics is claimed.

## Intake correction and unresolved official steps

PR #443 is currently open and unmerged. Its diff changes only one catalog entry's proof and attribution fields; its proposed Yes status does not mean upstream acceptance. Related PR #930 is closed and unmerged; its stated proof claims are not independently certified here. The prior complete upstream public formalization is explicitly disclosed regardless of its authors' prize participation.

The old PR body lacked several current required headings and structured proof JSON; the new draft supplies them, exact original-statement correspondence, the solver-first prerequisite, four verification judgments and explicit self-check evidence through the shared placeholder. Claim #1467 gains the required merged-PR field with its checkbox left unchecked, and refers to the PR for proof evidence. Existing submission and claim history are preserved. Solver registration, contribution/identity review, merge and the historical before-opening self-check cannot be retrospectively completed by replacing the text.
