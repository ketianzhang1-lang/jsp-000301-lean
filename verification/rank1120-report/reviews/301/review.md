# JSP-000301 — semantic and provenance review

**Pre-execution conclusion: semantic correspondence is established; fresh mechanical validation remains pending.** The selected proof gives a complete negative answer to this catalog's universal yes/no assertion. This does not settle the different counting question in Erdős Problem 365 or determine award eligibility.

1. **Original problem correspondence:** yes, statically reviewed against the fixed catalog entry and literal prime-divisor/square predicates.
2. **Exact selected commit actually verified in this batch:** pending the recorded isolated execution.
3. **Complete original scope:** the two final theorems cover the entire yes/no question by counterexample; the final executed verdict remains gated on the checks.
4. **Lean acceptance completeness:** not yet confirmed until fresh construction, target, replay and checker evidence is inspected.

## Fixed inputs

- Original problem: [catalog JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/problems/catalog-0301-0400.md#JSP-000301), including the 2026-09-13 record-correction note.
- Awards PR: [#187](https://github.com/TheJustinSunPrize/awards/pull/187), observed head `096e9cd0e3120181dce16ebfcc63c09eea92ddb8`; one catalog file, only Lean proof/Attribution basis changed. Original problem, status, and eligibility have not been narrowed or silently changed.
- Selected proof: repository `ketianzhang1-lang/jsp-000301-lean`, branch `main`, root project, exact commit `e1a17b0d6728b9d4929d1d4abd3721a27377369a`.
- The later strict verifier commit `26282f3afe1d23d35afda21cbecbc2f918043c6a` is an evidence version, not a new mathematical proof version. It claims the same eight public declarations of the unchanged original source. This batch checks those eight at the exact original proof commit.
- Mathematical evidence: Solomon W. Golomb, *Powerful Numbers*, American Mathematical Monthly 77(8) (1970), 848–852, [DOI](https://doi.org/10.2307/2317020). Fresh JSTOR access did not expose the article text. No claim of a fresh full-paper review is made. The catalog explicitly limits this problem to the yes/no assertion and states the witness; the mathematical witness can also be directly checked without relying on an inaccessible paper.

## Independently stated obligations and coverage

| Original obligation | Exact source declaration | Independent bridge and meaning |
|---|---|---|
| Consecutive positive integers | `JSP000301.jsp_000301_counterexample` | `Verify301.positive_pair` requires `0<n` and uses exactly `n+1`; positivity of the successor follows arithmetically. |
| Both powerful | `Powerful`, `powerful_12167`, `powerful_12168` | Literal `∀p, Nat.Prime p → p∣n → p*p∣n`, with no substitute number-theory property. |
| Neither is a perfect square | `PerfectSquare`, `not_square_12167`, `not_square_12168` | Negation of existence of any natural `m` with `m*m=n`; no bounded search or restriction on candidate square roots. |
| Refute the full universal assertion | `jsp_000301_disproved` | `Verify301.original_question_false` states the original universal claim with literal predicates and negates it. |
| Concrete witness arithmetic | Four supporting lemmas | `Verify301.witness_arithmetic` directly proves the two prime-power products and the strict interval between consecutive squares. |

The factorization 12167=23³ and 12168=2³·3²·13² makes every prime exponent at least two. Both integers lie between 110² and 111². The original proof obtains prime divisors from the displayed products and uses Mathlib's square interval theorem, then proves the logical negation directly. There are no extra hypotheses, finite-search assumptions, or class/section parameters. Defining powerfulness also at zero is harmless because the original and bridge conclusions require positive `n`.

## Reproduction design and trust boundary

- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; all nine package revisions come from the selected committed manifest.
- The original selected commit has no strict Python verifier. Therefore `harness/301-original.py` is an explicitly auditor-owned script, run separately from the tracked proof; no verifier script from a later commit is quietly presented as belonging to `e1a17...`.
- Clean original build, strict source compilation, original module kernel replay, all eight original public declarations' `#check`, `#print`, and `#print axioms`, dependency revision checks, and rejected `1=0` negative control precede the unmodified official target audit.
- Eleven target entries: eight original declarations (two definitions, four supporting lemmas, two endpoints), plus three auditor bridges. Every target is connected to the obligation matrix. The bridges live under the configured `JSP000301` library as untracked audit files.
- A strict precheck, official target audit, bridge kernel replay and NaNoda closure check are required. Only standard `propext`, `Classical.choice`, `Quot.sound` may be observed; no `native_decide`, `sorryAx`, added axiom, bypass option, external implementation or fabricated output occurs in the selected mathematical source. Static scanning is only a clue; actual closure evidence is still required.
- Historical whole-environment NaNoda evidence had a pretty-printer issue and a wider allowlist. The later eight-closure strict result is separate historical evidence. Neither is mislabeled as this batch's completed lean-verify result.

## Attribution, licenses and procedural limits

The selected file is a separately written implementation using Mathlib; no other submitter's Lean project is imported. The root code license is MIT and its notice must be retained. Mathlib and its dependencies keep their own notices. Mathematical credit remains Golomb's; the GitHub account requests only its own implementation and verification contribution with disclosed OpenAI ChatGPT/Codex assistance.

The existing claim discloses overlapping evidence including Issue #25 and numerous earlier claims. Neither implementation independence, code size, nor PR date proves worldwide priority. The PR is pending, solver registration and source attribution remain official review steps, and the historical “self-check before opening this PR” checkbox cannot truthfully be retrospectively checked. The claim's merged-PR declaration stays unchecked. No candidate, review period, written identity confirmation, award, or payment is asserted.
