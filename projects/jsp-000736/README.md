# JSP-000736 / Erdős 885: the known k = 4 case

This package formalizes the known result of Andrew Bremner (2019): four distinct
positive integers have at least four common complementary-factor differences.
It proves exactly `erdos_885.variants.k_eq_4` from Formal Conjectures, with its
original definition, up to namespace names. `Challenge.lean` checks this by
elaboration against a separately stated copy of the source statement.

This is a **partial-scope formalization contribution** relative to the full
JSP-000736 / Erdős 885 problem. It does not prove the assertion for arbitrary k,
settle k = 5, or establish arbitrarily large intersections. No new mathematical
result or globally first formalization is claimed.

## Certificate

The four positive integers are 26128575, 291722431, 561117375, 713526975.
The four common differences are 126, 16110, 33390, 75390.
`common_differences` supplies all sixteen explicit complementary factor pairs.
`factorDifferenceSet_finite` establishes the finiteness needed to interpret
`Set.ncard` correctly. The main theorem proves positivity, distinctness and
intersection cardinality, without any unproved hypotheses.

## Sources and credit

- Mathematical result: Andrew Bremner, *On a problem of Erdős related to common
  factor differences* (2019), [DOI](https://doi.org/10.1142/S1793042119500581).
- Definition and target, copyright 2026 The Formal Conjectures Authors,
  Apache-2.0: [pinned Erdős 885 source](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/885.lean).
- The concrete numbers were found in Patrick White's report, which credits
  Bremner and discloses Claude assistance:
  [July 27, 2026 report](https://erdosproblemaday.com/day/885-factor-difference-k5).
  The publisher paper itself was not available to inspect. Attribution of the
  particular numerical witness follows that report. All sixteen factor pairs
  were independently recomputed and verified here.
- [Official catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000736).
- Related [official PR 297](https://github.com/TheJustinSunPrize/awards/pull/297)
  covers k = 2 and k = 3 and expressly does not cover k = 4. Its proof code was
  not used. This checked overlap is not a proof of global priority.

The source definition and target retain their original attribution. The proof
implementation was produced with OpenAI ChatGPT assistance under the submitting
account ketianzhang1-lang. Verification scripts adapt that account's earlier
submission infrastructure. This is a self-submission with an interest in the
outcome. Proposed recipient: `RECIPIENT-JSP-000736-KZ-A`, identity confirmation
pending. No independent human review, award amount, eligibility decision or
payment entitlement is asserted. The organizers must assess incremental value,
priority, attribution and award eligibility.

## Reproduction

Use Lean 4.34.0 and the committed manifest (Mathlib and all transitive Git
revisions pinned). From this directory:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script compiles with warnings treated as errors, rechecks the module
with leanchecker, audits all ten theorems against the standard axiom allowlist
(propext, Classical.choice, Quot.sound), verifies the source statement and
manifest revisions, and checks rejection of false arithmetic. No `sorry`,
custom axiom or `native_decide` is used in the submitted proof.
The second script exports the proof closure and checks it with pinned NaNoda,
hard-failing on any nonstandard axiom. Its evidence includes the export digest
and the independent checker's printed target statement.

CI uses network access and the standard Mathlib cache; a full offline rebuild
of all dependencies is not claimed. Refer to the linked run and its artifacts
for actual validation status. Passing software checks is separate from prize
acceptance.

## Dilation supplement (September 17, 2026)

`JSP000736Scaling.lean` adds a fully quantified elementary extension of the
existing certificate. For every positive natural t, multiply the four integers
by t² and the four differences by t. Factoring t²n as (ta)(tb) proves the
transport of every complementary-factor difference. Positive multiplication
preserves distinctness. The supplemented theorems prove:

1. Every positive scale satisfies the original k = 4 cardinality statement.
2. For every natural bound M, there are four distinct integers and four common
   differences, all greater than M.
3. There are infinitely many distinct four-integer witness sets. Injectivity
   is proved by taking the sum of each scaled set.

The new module is checked by `ScalingAudit.lean` and a separately restated
mathematical specification in `ScalingChallenge.lean`. The main module and
its sixteen factor-pair certificates are unchanged.

These are elementary consequences of the cited Bremner construction, not new
mathematics or another award claim. Arbitrarily large **values** do not establish
arbitrarily many common differences: the number guaranteed here remains four.
The general problem and k = 5 are still outside this submission's scope. This
supplement belongs to the existing [official PR 347](https://github.com/TheJustinSunPrize/awards/pull/347).
