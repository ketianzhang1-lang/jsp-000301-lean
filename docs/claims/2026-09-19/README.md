# Review supplement for JSP-000391 and JSP-000438

Prepared on 2026-09-19 for the existing applications by ketianzhang1-lang. This document supplies current attribution clarification and a review index. It is not an identity-verification outcome, award announcement, or new claim.

## Applicant and contribution attribution

The applicant account is [ketianzhang1-lang](https://github.com/ketianzhang1-lang), the owner of the original development repository and author of [claim #1352](https://github.com/TheJustinSunPrize/awards/issues/1352) and [claim #1410](https://github.com/TheJustinSunPrize/awards/issues/1410). The personal name used in the existing 438 source attribution is **Ketian Zhang**. This note explicitly associates that applicant account with the named contributor for review.

The applicant selected and directed these AI-assisted formalization projects and submitted their results. Lean implementation, proof development, and machine verification were carried out with OpenAI ChatGPT/Codex assistance. This is not a claim that the applicant manually wrote every proof or independently checked every inference. References to "we" or "our" in the submission documentation describe this AI-assisted project and do not establish an additional verified human recipient.

For 391, the claimed contribution is the independently developed arbitrary-base recurrence formalization, normalization, digit identities and bounds, reconstruction, admissible-shift result, and verification package. The mathematical construction is Thomas Stoll's, and the earlier binary formalization and Mathlib retain their credit.

For 438, the claimed contribution is the downstream all-order Ramsey integration, statement alignment, compatibility port, even-order star sharpness, finite-color supplement, and verification package. The Erdős–Sós proof and Formal Conjectures definitions retain their original authorship and licenses; they are not claimed as newly authored by this applicant.

This is a current applicant-side attribution clarification, not independent corroboration or a backdated source record. Historical sources, account-authored submissions, the existing proof headers, and maintainer verification remain material. A fresh challenge or private corroborating evidence should use the maintainer-designated process.

## Existing applications and source versions

| Problem | Existing PR | Existing claim | Selected proof version |
| --- | --- | --- | --- |
| JSP-000391 | [#293](https://github.com/TheJustinSunPrize/awards/pull/293) | [#1352](https://github.com/TheJustinSunPrize/awards/issues/1352) | [14e5155e68554de4e053e4aacd77095a93e96dd4](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/14e5155e68554de4e053e4aacd77095a93e96dd4/projects/jsp-000391) |
| JSP-000438 main and sharpness | [#408](https://github.com/TheJustinSunPrize/awards/pull/408) | [#1410](https://github.com/TheJustinSunPrize/awards/issues/1410) | [5f94d026ec88696bb5047506c433ad401e5f02ef](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438) |
| JSP-000438 finite-color supplement | Same PR | Same claim | [0175b2a7a50f7687ece92f61bbe0e3a2f377913a](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/0175b2a7a50f7687ece92f61bbe0e3a2f377913a/projects/jsp-000438) |

The proof snapshots are unchanged by this supplement. The repository name refers to its first project; the table's project paths identify the actual 391 and 438 sources. It is a multi-project original development repository.

## Scope and verification index

### JSP-000391

The endpoint JSP000391.stoll_general_base quantifies over every radix g >= 2, positive real target w, admissible shift, and digit index. The recurrence is defined recursively, and the proof establishes the digit identities, bounds, and reconstruction convergence. JSP000391.jsp000391 provides an explicit admissible shift, avoiding an empty-parameter statement.

The [statement and contribution documentation](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5d2b0e94d01867a96de34ca96c335d2602b27d4e/projects/jsp-000391/README.md) describes normalization and the exact relationship with Stoll's Theorem 1.3.

[Run 35252880778](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35252880778) remains successful and its head is the selected proof commit. The pinned [eight-target axiom log](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/14e5155e68554de4e053e4aacd77095a93e96dd4/projects/jsp-000391/evidence/axioms.log) lists only propext, Classical.choice, and Quot.sound.

### JSP-000438

The main endpoint Erdos547.erdos_547 proves the diagonal tree Ramsey bound R(T,T) <= 2n-2 for every n >= 2 and every n-vertex tree, using a proved and credited Erdős–Sós dependency. The direct containment theorem supplies a member of the defining Ramsey set; this does not use the empty-set convention of a natural infimum.

[Statement alignment](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438/STATEMENT.md) records the exact quantifiers and non-induced injective containment. The sharpness theorem supplies equality for stars at every even order, including two. It does not claim an exact formula for every individual tree.

[Main/sharpness run 35177382098](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177382098) remains successful at its selected commit. The verification job records successful build/replay, ten axiom audits, negative control, and NaNoda checking. [Finite-color run 35177218300](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177218300) remains successful at its separate selected commit.

These are historical contributor-run checks whose current metadata was rechecked. This supplement is not a new Lean build or an independent human certification. [Dependency attribution and port record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438/UPSTREAM_PORT.md) remain part of the submission.

## Relative priority and current overlap

The [fixed 2026-09-18 evidence package](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/377c25f075326ecfd0aac8cc91859403b8578a42/docs/priority/2026-09-18/README.md) links historical PR source bundles, early CI, selected versions, identical core-source Git blobs, and timestamp limitations.

For 391, the early verification completed on 2026-09-16 at 22:33:05 UTC, and PR #293 was created at 22:43:45 UTC. For 438, early all-order verification completed on 2026-09-17 at 02:38:50 UTC, and PR #408 was created at 02:51:34 UTC. The later 438 supplements are not backdated to that early run.

A targeted official-repository search on 2026-09-19 returned the following 391 PRs:

| PR | Inspected scope and relevance |
| --- | --- |
| [#293](https://github.com/TheJustinSunPrize/awards/pull/293) | This applicant's complete arbitrary-base construction. |
| [#1134](https://github.com/TheJustinSunPrize/awards/pull/1134) | Its description covers selected decimal digit examples; it does not state the same universal recurrence theorem. |
| [#1163](https://github.com/TheJustinSunPrize/awards/pull/1163) | A later complete arbitrary-base implementation. Its description and [pinned NOTICE](https://github.com/PengSafari/jsp-000391-lean/blob/8beb80bbe38682395de5afb7b33e7fa05ad72637/NOTICE.md) acknowledge reading #293 and the exact earlier proof source. No first-formalization priority is asserted there. |
| [#1520](https://github.com/TheJustinSunPrize/awards/pull/1520) | Another submitter's catalog reference to the same PengSafari source; its author identifies themselves as catalog editor, not proof author. |
| [#1587](https://github.com/TheJustinSunPrize/awards/pull/1587) | Its [pinned Jsp391Full.lean](https://github.com/shunfeng8421/jsp301-lean/blob/e8872b9b405206ce100f5131a9ce744a6f0c9d32/Jsp391Full.lean) proves that differences in one integer recurrence belong to {0,1} for n >= 2. That file does not establish arbitrary-base coverage or a reconstruction theorem identifying those digits with the desired target. This is a scope distinction, not an allegation about the contributor. |

PR #1587 was open and unmerged when checked. The phrase "confirmed recipient" in an applicant-authored title is not itself maintainer verification or an award announcement.

For 438, the exact-JSP official-repository PR search returned #408 only. This limited search does not exclude differently named submissions or external proofs. The earlier sufficiently-large/conditional treatment and the reused Erdős–Sós source remain disclosed.

The evidence supports relative-priority review, particularly the other project's explicit acknowledgement for 391. Git timestamps, CI timestamps, and current PR membership do not by themselves establish exact first public visibility or global first completion.

## Review requests and outstanding decisions

1. Verify that each pinned complete statement matches the original problem and review the attributable formalization work separately from credited upstream mathematics.
2. Assess the existing relative-priority evidence and distinguish complete arbitrary-base coverage from selected examples or digit-range lemmas.
3. For 438, review the proposed Open-to-Solved catalog correction supported by the complete all-order theorem and even-order sharpness. This is not a nomination of the applicant as the mathematical discoverer of Erdős–Sós or the classical Ramsey implication.
4. Resolve account-to-contributor verification and reconcile the catalog's Lean-proof and eligibility fields before claim approval.
5. Record any award decision through the organizers' verification and announcement process.

At inspection both existing claims and catalog PRs were open, no maintainer review was recorded on the PRs, and each claim's sole comment was the applicant's priority supplement. The main catalog still showed Lean proof: No and Eligible to claim: No for both entries; 391 was Solved and 438 was Open.

Only the maintainers can confirm verification, eligibility, an award, and payment arrangements. This supplement creates no verified-recipient record, sets no payment amount, and claims no guaranteed award.
