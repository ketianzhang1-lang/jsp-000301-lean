# Ready-to-create pull request

The complete PR branch is published. Automated creation in TheJustinSunPrize/awards
returned HTTP 403: `Resource not accessible by integration`. **The automated attempt
did not create a PR.**

[Create the prepared PR — title and complete body prefilled](https://github.com/TheJustinSunPrize/awards/compare/main...ketianzhang1-lang:awards:jsp-000585-catlin-sharp-kz?expand=1&title=JSP-000585%3A%20exact%20Catlin%20graph%20formalization%20and%20verification%20(scoped)&body=%23%23%20Purpose%20and%20scope%0A%0ARelated%20to%20%23417.%0A%0AThis%20PR%20supplies%20the%20reproducible%20source%20and%20verification%20package%20for%20the%20existing%20Catlin%20contribution%20recommendation.%20For%20the%20explicit%2015-vertex%20graph%20C5%5BK3%5D%2C%20it%20proves%20Mathlib%20chromatic%20number%208%20and%2C%20for%20every%20natural%20r%2C%20existence%20of%20a%20K_r%20subdivision%20if%20and%20only%20if%20r%20%3C%3D%207.%0A%0AThe%20contribution%20is%20a%20scoped%20finite%20formalization%20related%20to%20JSP-000585%20%2F%20Erdos%20717.%20It%20does%20not%20prove%20the%20original%20uniform%20asymptotic%20bound%20for%20arbitrary%20graphs.%20Please%20assess%20scoped-contribution%20eligibility%20and%20overlap.%0A%0A%23%23%20Changes%0A%0AAdds%20%60docs%2Fsubmissions%2Fjsp-000585-catlin-sharp-kz%2F%60%20with%20seven%20proof%20modules%2C%20twelve%20theorem%20audits%2C%20pinned%20dependencies%2C%20reproduction%20scripts%2C%20proof%20explanations%2C%20provenance%2C%20verification%20receipt%20and%20source%20checksums.%20The%20subdivision%20model%20uses%20actual%20simple%20graph%20paths%20with%20pairwise%20disjoint%20interiors%20avoiding%20every%20branch%20vertex.%0A%0AThe%20new%20K7%20construction%20and%20branch-set%20restriction%20complete%20the%20exact%20classification.%20The%20package%20also%20includes%20the%20clean-build%20module-registration%20fix.%20PROVENANCE.md%20supplies%20the%20attribution%20document%20missing%20from%20the%20earlier%20public%20package%3B%20the%20review%20documents%20now%20reference%20the%20existing%20Issue%20%23417.%0A%0A%23%23%20Verification%0A%0AThe%2013%20proof%2Fbuild%2Fchecking%20files%20match%20the%20successful%20tested%20source%20byte%20for%20byte%2C%20as%20recorded%20in%20SOURCE_MAP.md.%0A%0A-%20Tested%20commit%3A%20%60019467ead20f2d6b87e672a1dfef7d5b8886febf%60.%0A-%20%5BProof%20workflow%5D(https%3A%2F%2Fgithub.com%2Fketianzhang1-lang%2Fjsp-000301-lean%2Factions%2Fruns%2F35176307046)%3A%20clean%20build%2C%20seven%20kernel%20replays%2C%20twelve%20axiom%20audits%2C%20dependency-revision%20checks%20and%20rejected%20false-arithmetic%20control%20passed.%0A-%20NaNoda%20checked%207%2C621%20declarations%20with%20no%20errors.%20RECEIPT.md%20records%20artifact%20ID%2C%20SHA-256%2C%20size%20and%20retention.%0A-%20Awards%20repository%20checks%3A%20validate%2C%20links%2C%20build%20and%20check%20all%20passed%3B%2022%20existing%20unit%20tests%20passed.%20Generated%20data%20is%20unchanged.%0A-%20Package%20SHA-256%20checks%20and%20diff%20whitespace%20checks%20passed.%0A%0A%23%23%20Attribution%20and%20requested%20review%0A%0AClassical%20mathematics%20is%20credited%20to%20Catlin.%20Formalization%20was%20prepared%20with%20OpenAI%20ChatGPT%20assistance%3B%20code%20lineage%20and%20existing%20external%20Erdos%20717%20work%20are%20disclosed%20in%20PROVENANCE.md.%0A%0AThe%20proposed%20contributor%20remains%20%60RECIPIENT-JSP-000585-CATLIN-KZ-A%60%2C%20with%20confirmation%20pending.%20This%20is%20a%20self-submission%3B%20no%20mathematical%20novelty%2C%20first-formalization%20priority%2C%20independent%20human%20sign-off%20or%20award%20entitlement%20is%20claimed.%20The%20PR%20changes%20no%20catalog%20flag%2C%20candidate%20record%2C%20award%20or%20payment%20status.%0A)

Confirm the destination is `TheJustinSunPrize/awards:main` and the source is
`ketianzhang1-lang/awards:jsp-000585-catlin-sharp-kz`, then click **Create pull request**.
After creation, GitHub will display the PR number and URL.

- Existing recipient recommendation: https://github.com/TheJustinSunPrize/awards/issues/417
- Published source branch: https://github.com/ketianzhang1-lang/awards/tree/jsp-000585-catlin-sharp-kz
- Immutable submission commit: `9237a0d47f2976277bc93375c523be36ced3d998`
- Comparison: one commit ahead, zero behind, exactly 22 added files in `docs/submissions/jsp-000585-catlin-sharp-kz/`.
- Validation, local links, data build/check, all 22 existing unit tests, source identity and package checksums passed.
- The 13 proof/build/checking files are byte-identical to the previously successful Lean/NaNoda source.

## PR title

JSP-000585: exact Catlin graph formalization and verification (scoped)

## Complete PR body

## Purpose and scope

Related to #417.

This PR supplies the reproducible source and verification package for the existing Catlin contribution recommendation. For the explicit 15-vertex graph C5[K3], it proves Mathlib chromatic number 8 and, for every natural r, existence of a K_r subdivision if and only if r <= 7.

The contribution is a scoped finite formalization related to JSP-000585 / Erdos 717. It does not prove the original uniform asymptotic bound for arbitrary graphs. Please assess scoped-contribution eligibility and overlap.

## Changes

Adds `docs/submissions/jsp-000585-catlin-sharp-kz/` with seven proof modules, twelve theorem audits, pinned dependencies, reproduction scripts, proof explanations, provenance, verification receipt and source checksums. The subdivision model uses actual simple graph paths with pairwise disjoint interiors avoiding every branch vertex.

The new K7 construction and branch-set restriction complete the exact classification. The package also includes the clean-build module-registration fix. PROVENANCE.md supplies the attribution document missing from the earlier public package; the review documents now reference the existing Issue #417.

## Verification

The 13 proof/build/checking files match the successful tested source byte for byte, as recorded in SOURCE_MAP.md.

- Tested commit: `019467ead20f2d6b87e672a1dfef7d5b8886febf`.
- [Proof workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176307046): clean build, seven kernel replays, twelve axiom audits, dependency-revision checks and rejected false-arithmetic control passed.
- NaNoda checked 7,621 declarations with no errors. RECEIPT.md records artifact ID, SHA-256, size and retention.
- Awards repository checks: validate, links, build and check all passed; 22 existing unit tests passed. Generated data is unchanged.
- Package SHA-256 checks and diff whitespace checks passed.

## Attribution and requested review

Classical mathematics is credited to Catlin. Formalization was prepared with OpenAI ChatGPT assistance; code lineage and existing external Erdos 717 work are disclosed in PROVENANCE.md.

The proposed contributor remains `RECIPIENT-JSP-000585-CATLIN-KZ-A`, with confirmation pending. This is a self-submission; no mathematical novelty, first-formalization priority, independent human sign-off or award entitlement is claimed. The PR changes no catalog flag, candidate record, award or payment status.

