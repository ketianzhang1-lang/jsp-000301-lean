# JSP-000530: scope review and requested determination

Review date: 18 September 2026. Contributor account: `ketianzhang1-lang`.

## Conclusion

We have a complete Lean disproof of the near-n pinned-distance assertion under the no-four-concyclic hypothesis alone. We have not completed every historical question associated with Erdős 654. The current prize catalog does not specify the numerical threshold in its wording, and no maintainer scope determination was present in PR #348's discussion at this review.

The next step is a precise scope determination. We do not classify the current package as an accepted complete-solution submission or claim first-formalization priority.

## Statements that must be distinguished

For a finite planar set S, put n = |S|, let d_S(p) count the distinct distances from p to S excluding p itself, and put D(S) = max d_S(p) over p in S.

| Target | Hypotheses and conclusion | Existing package |
| --- | --- | --- |
| Near-n assertion | Every sufficiently large S with no four concyclic points has a point with at least (1-epsilon)n distances, for every positive epsilon. | Disproved by our existing quantified theorem. |
| General-position upper construction | Arbitrarily large configurations with no three collinear and no four concyclic points, and D(S) < (1-c)n for a fixed positive c. | Not established. Our two-axis family has collinear triples. |
| Uniform lower improvement | A fixed positive c, independent of the set and its size, improves the guarantee to D(S) > (1+c)n/3. | Neither proved nor disproved by the two-axis result. This remains a separate question even under the no-four-concyclic hypothesis alone. |

[Erdős (1987), printed page 168, equations (3) and (4)](https://www.renyi.hu/~p_erdos/1987-27.pdf#page=2) separates the lower-improvement question from the upper-construction question, initially in general position. The following paragraph also asks whether the lower improvement holds with only the circle restriction. We inspected the scanned page, including both inequality signs. Equation (5) asks a related summed-distance question; we do not assert that every adjacent question belongs to the prize entry.

[Feng et al., Section 3.1, Remark 3.1](https://arxiv.org/html/2601.22401v3#S3.SS1) describes the two-axis result as partial relative to the collection of formulations, and rejects the additional general-position argument from the raw model output. That paper attributes the near-n formulation to Erdős (1997), printed page 530. We did not obtain and independently inspect that 1997 page in this review.

The [current catalog entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000530) asks about sufficiently many distinct distances without specifying which threshold, records a date no later than 1987, and remains Open with Lean proof No. Its abbreviated wording alone does not select the near-n statement or establish that all historical variants are required.

## What our checked source establishes

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000530-two-axis`.
- Verified proof commit: `fb8577233935d1ff4533418ff8ea33a4d7dab101`.
- File: [projects/jsp-000530/JSP000530.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fb8577233935d1ff4533418ff8ea33a4d7dab101/projects/jsp-000530/JSP000530.lean).
- Endpoints: `JSP000530.counterexample_family` and `JSP000530.not_asymptotically_all_distances`.

For every natural m, the family has 4m points, at most three points on any Euclidean circle, and fewer than 3m distinct nonzero distances from every point. The asymptotic endpoint negates the full epsilon/N assertion. It uses the complex plane with its Euclidean metric, arbitrary circle centers and radii, and excludes the base point from the distance count.

The construction uses points (plus or minus 2(i+1), 0) and (0, plus or minus (2i+1)) for 0 <= i < m. For m >= 2, each axis contains at least four points. Thus the source does not provide a general-position example.

A bound below 3n/4 for these examples does not refute every possible fixed improvement above n/3. The quantifiers and constants differ. Removing collinearities would still leave that lower-bound question to settle.

## Existing research and verification

The [research record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/0cedcd9996abd02eb8b64393d4b879cbf8c6eceb/projects/jsp-000530/research/PROGRESS.md) already records fifteen auxiliary Lean lemmas: a distance-group slack reduction, perpendicular-bisector obstructions, and failure of a quadratic-bending attempt. These are prior research additions, not a new complete solution produced by this review.

The [hosted proof run 35169007348](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169007348) reports success at proof commit `fb8577233935d1ff4533418ff8ea33a4d7dab101`; it was created on 17 September 2026 at 01:02:55 UTC and last updated at 01:05:18 UTC. The existing verification record describes kernel replay, six axiom audits and NaNoda checking of 13,905 declarations.

This review compared `JSP000530.lean` at the verified proof commit with the current branch source and found identical text. It did not rerun the complete proof closure. The current pre-review documentation head was `220b42feb00244691b8823db56b04b9d49c89b22`; its README already documents the additional lower-bound gap. The public PR body had not yet incorporated that correction.

## Attribution and priority

We contribute the independently written even/odd-coordinate Lean implementation, its geometric and counting proofs, the quantified negation and verification package, with OpenAI ChatGPT assistance. Mathematical credit for the two-axis construction remains with Aletheia and the authors of the cited paper. The source attribution is recorded in [PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/220b42feb00244691b8823db56b04b9d49c89b22/projects/jsp-000530/PROVENANCE.md).

PR #348 was created on 17 September 2026 at 01:11:33 UTC. Its current text and creation time do not establish when every statement in the editable body was first public. A currently public CI record also does not, by itself, certify that the repository was public at execution time. Neither record establishes worldwide first completion.

The [Selection Rules, sections 5 and 6](https://www.hejustinsun.com/zh/prize/rules) address priority and official verification. The [current repository submission instructions](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions) require complete original-problem scope. We cannot resolve the catalog's scope ambiguity by changing its status ourselves.

## Precise determination requested

Does JSP-000530 treat the near-n assertion with only the no-four-concyclic hypothesis as a separate complete target, or does it require the historical uniform lower improvement and/or the general-position question?

If the near-n assertion is the accepted complete target, please identify its source and exact quantitative statement. We can then align the existing theorem, attribution and catalog-only diff with that determination for full review. If the broader historical questions are required, this package remains incomplete and should not be marked complete or eligible on the strength of the two-axis theorem.

This request seeks clarification of the existing target; it does not request that the problem be weakened to fit our proof. No scope ruling, first-priority ruling or award decision is assumed.
