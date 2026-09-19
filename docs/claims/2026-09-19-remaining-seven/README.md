# Review supplement for seven existing award claims

Prepared on 2026-09-19 under GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. This supplement makes the submitted contributions and their dependency boundaries easier to inspect. It updates existing submissions; it does not create new claims or assert new mathematical priority.

## Submission and source mapping

| Problem | Existing claim | Existing catalog PR | Selected proof commit |
| --- | --- | --- | --- |
| JSP-000301 | [#1413](https://github.com/TheJustinSunPrize/awards/issues/1413) | [#187](https://github.com/TheJustinSunPrize/awards/pull/187) | [`e1a17b0d6728b9d4929d1d4abd3721a27377369a`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/e1a17b0d6728b9d4929d1d4abd3721a27377369a/) |
| JSP-000388 | [#1475](https://github.com/TheJustinSunPrize/awards/issues/1475) | [#343](https://github.com/TheJustinSunPrize/awards/pull/343) | [`a9eae7a01edade3d5d9a386144dcd2848b4de917`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/a9eae7a01edade3d5d9a386144dcd2848b4de917/projects/jsp-000388) |
| JSP-000725 | [#1412](https://github.com/TheJustinSunPrize/awards/issues/1412) | [#361](https://github.com/TheJustinSunPrize/awards/pull/361) | [`d0d37952bba030d7c8a68f000094e0d601d9fed7`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/d0d37952bba030d7c8a68f000094e0d601d9fed7/projects/jsp-000725) |
| JSP-000140 | [#1467](https://github.com/TheJustinSunPrize/awards/issues/1467) | [#443](https://github.com/TheJustinSunPrize/awards/pull/443) | [`724a733a2b498d7b3b956e66b76d7334cc906eaf`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/724a733a2b498d7b3b956e66b76d7334cc906eaf/projects/jsp-000140) |
| JSP-000554 | [#1577](https://github.com/TheJustinSunPrize/awards/issues/1577) | [#369](https://github.com/TheJustinSunPrize/awards/pull/369) | [`21fcf006fd68b0bead9f979b704c92032f05cba8`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/21fcf006fd68b0bead9f979b704c92032f05cba8/projects/jsp-000554) |
| JSP-000585 | [#1584](https://github.com/TheJustinSunPrize/awards/issues/1584) | [#432](https://github.com/TheJustinSunPrize/awards/pull/432) | [`9661ef0f170e750b1ac2153b9017bad86044680c`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research) |
| JSP-000907 | [#1588](https://github.com/TheJustinSunPrize/awards/issues/1588) | [#696](https://github.com/TheJustinSunPrize/awards/pull/696) | [`555ce4f13bf7e8e8557020728f7f97ad3d1f51e0`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/555ce4f13bf7e8e8557020728f7f97ad3d1f51e0/projects/jsp-000907) |

The containing repository's historical name refers to JSP-000301; the other six projects use their own directories. An owned repository is not proof of original authorship of imported work. The selected sources retain the original notices and distinguish our implementation/integration from reused results.

## Source comparison that was executed

`python3 verify_evidence.py` verifies [120 immutable file snapshots](sources.json): byte lengths, SHA-256 and Git blob hashes. The executed comparisons confirmed:

- 46 selected-to-later file bindings, including every listed local proof module, dependency manifest, toolchain/lakefile and imported-source manifest where a later revision is linked.
- Eleven original Lean modules unchanged in the complete submissions: one each for 140, 388, 554 and 725, and seven for 585; the twelfth historical comparison is 907's research note.
- Four unchanged 301 proof/configuration files connecting the original proof pin to the new strict verification commit.
- The six reused upstream root modules reproduce their recorded compatibility-port hashes, including modification notices, from the pinned upstream bytes. This is not a new check of every transitive module.

Full Lean/NaNoda verification is recorded separately below. The source comparator does not execute Lean, prove authorship, establish global priority or determine an award. Source-preservation history documents what remained unchanged; it does not alone establish that a contribution predates every competing submission.

## JSP-000301

The complete yes/no endpoint uses the actual prime-divisor definition of powerfulness and natural-number squares. The explicit positive witness is 12167 = 23³ and 12168 = 2³·3²·13², with both values strictly between 110² and 111². `jsp_000301_counterexample` supplies all four property proofs; `jsp_000301_disproved` negates the universal assertion. A single counterexample settles this catalog question; the separate counting question is outside its scope.

Our separately implemented source uses Mathlib, without importing another submitter's project. Its mathematical counterexample is credited to Golomb, *Powerful numbers* (1970), as recorded in [the provenance record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/86a5a9af1e07874c2346e7da1a82cf0c35ca28bb/PROVENANCE.md). The eight selected public targets are two predicate definitions and six proved statements. This count differs intentionally from the older nine-declaration automatic namespace audit, which also included generated material.

**New executed verification:** [run 35413514755](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35413514755), verification commit `26282f3afe1d23d35afda21cbecbc2f918043c6a` on `jsp-000301-strict-verification-20260919`, succeeded on 2026-09-19. The build, bundled kernel replay, eight target axiom reports, nine actual dependency revisions and false-arithmetic negative control passed. NaNoda checked **3,487 declarations** from the eight selected dependency closures, with only `propext`, `Classical.choice`, `Quot.sound` permitted and `unpermitted_axiom_hard_error=true`. The checker reported no errors, and nonempty printed statements were required. Source, lakefile, toolchain and dependency manifest match the original selected commit byte-for-byte.

The earlier [run 35131699133](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133) checked 188,335 whole-environment declarations but emitted a pretty-printer error and used a broader environment allowlist. That historical limitation remains disclosed. The new targeted export supplies the stricter theorem-closure result; **3,487 is not a repeated check of the old 188,335-declaration export**. See [the new receipt](301-strict-receipt.json) and the [strict audit source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/26282f3afe1d23d35afda21cbecbc2f918043c6a/Audit301Strict.lean).

## JSP-000388

Our original [quadratic obstruction](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a9eae7a01edade3d5d9a386144dcd2848b4de917/projects/jsp-000388/JSP000388.lean) remains byte-identical to commit `c32d8195dc69e19d9bcf96987543f306c71749f2`. It covers every `a*x²+b*x+c` with `a ≠ 0` and `a ∣ b`, including both signs of `a`; it does not classify every quadratic with arbitrary linear coefficient.

In [our integration module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a9eae7a01edade3d5d9a386144dcd2848b4de917/projects/jsp-000388/JSP000388Complete.lean), `exactComplement_iff_tiling` identifies the pair-value predicate exactly. `exactComplement_translate` translates A by −c when values increase by c. `exists_shifted_polynomial_complement` supplies a complement for every `X^6+C(c)`. The endpoint `jsp_000388` uses `X^6`, degree at least two and unique pairs of **summand values** over all integers. It does not require a unique polynomial input, which would be false for sixth powers.

The affirmative existence theorem comes from the attributed 155-module Erdős 477 development. Its source credits Codex, Liam Price (GPT 5.6 Sol Pro), and the earlier Pengbinghui/pipeline-math criterion. Our quadratic obstruction is a separate result and is not needed to establish the affirmative sixth-power endpoint. The obstruction's mathematical sources and earlier [PR #61](https://github.com/TheJustinSunPrize/awards/pull/61) remain acknowledged in [the provenance record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a9eae7a01edade3d5d9a386144dcd2848b4de917/projects/jsp-000388/PROVENANCE.md).

**Receipt correction:** [run 35295466997](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35295466997) completed successfully at the selected commit on 2026-09-18. The actual job log reports **70,658 declarations checked with no errors** by strict-allowlist NaNoda, in addition to the complete source/replay/axiom steps. This result supersedes the old documentation's statement that hosted NaNoda success was not yet presumed. [The API/log receipt](388-hosted-receipt.json) binds the exact run, job, source and artifact. Its artifact ZIP digest is GitHub-reported; we have not relabeled it as a locally recomputed hash.

## JSP-000725

The original [interval construction and boundary obstruction](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/d0d37952bba030d7c8a68f000094e0d601d9fed7/projects/jsp-000725/JSP000725.lean) is byte-identical to commit `a197ebc6cc3ea878c60db0f2456465cef1e8e09b`. It is a concrete lower construction, with mathematical credit to Straus.

The [natural/integer bridge](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/d0d37952bba030d7c8a68f000094e0d601d9fed7/projects/jsp-000725/JSP000725Bridge.lean) proves admissibility and boundedness equivalences in both directions, including an integer set's natural preimage. `maxCard_eq_upstream` therefore compares the maxima over all admissible subsets, rather than only interval subsets.

In [the complete endpoint](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/d0d37952bba030d7c8a68f000094e0d601d9fed7/projects/jsp-000725/JSP000725Complete.lean), `terminalInterval_spec` directly uses our retained construction and proves a witness of size `Nat.sqrt (4*N+1)-1` for **every** N, including zero. The credited Erdős 874 upper proof yields `eventual_maxCard_exact`; combining it with the retained witness proves eventual optimality against **arbitrary** admissible subsets. The normalized limit is 2. The exact maximum is asserted only for sufficiently large N, and no explicit universal numerical cutoff is supplied.

This division agrees with Deshouillers–Freiman, [Theorem 1, p. 142](https://www.numdam.org/article/AST_1999__258__141_0.pdf). Their general upper theorem is not attributed to us. The 42-module imported closure credits Codex/GPT-5.6 Sol and its retained sources. The original interval proof is used in the complete maximizing-witness conclusion, rather than merely stored alongside it.

## JSP-000140

The original [strict finite lower-bound development](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/724a733a2b498d7b3b956e66b76d7334cc906eaf/projects/jsp-000140/JSP000140.lean) remains byte-identical to commit `b9c7f4e9dfe6b9f398533b02c4b93805e1abc8f1`. It yields `5*(n-1) < 6*minPalette n` and the integer bound `5*(n-1)/6+1 ≤ minPalette n` for n ≥ 4.

Our [edge-model bridge](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/724a733a2b498d7b3b956e66b76d7334cc906eaf/projects/jsp-000140/JSP000140Bridge.lean) maps symmetric pair colorings to genuine unordered edges and back. The reverse map needs a palette value for diagonal pairs, so `pairColorable_iff` and `minPalette_eq` correctly assume n ≥ 2. `minPalette_spec` proves the minimum is attained. The small n exception is explicitly handled instead of silently claiming equality of the two models there.

The [complete endpoint](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/724a733a2b498d7b3b956e66b76d7334cc906eaf/projects/jsp-000140/JSP000140Complete.lean) transports the credited Erdős 136 asymptotic theorem and combines it with our strict finite lower bound. `eventually_near_optimal` uses an attained minimum to produce actual colorings for every positive epsilon. The asymptotic limit 5/6 comes from the imported full development; our strict lower bound supplies an additional finite conclusion and is not the proof of the imported limit.

Mathematical credit for the complete asymptotic theorem remains with Bennett–Cushman–Dudek–Prałat and Joos–Mubayi, with earlier lower-bound sources retained. Codex/GPT-5.6 Sol retain formal credit for the 20-module imported development. See [the contribution record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/728526da93d79904fec57572a84e1202b5a8a93d/projects/jsp-000140/PROVENANCE.md).

## JSP-000554

Our original [23-theorem residue development](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/21fcf006fd68b0bead9f979b704c92032f05cba8/projects/jsp-000554/JSP000554.lean) is byte-identical to commit `2a6c737b5fb409a5600918cc5a2bab0a8dd174bb`. It includes the uniform `badGap_iff_residue_all`, counting identities and exact small-gap classifications. The restriction `h ≥ 2` is explicit; `badGap_start_ge_length` supplies the previously needed starting-point condition when an exceptional gap actually exists.

The [complete integration](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/21fcf006fd68b0bead9f979b704c92032f05cba8/projects/jsp-000554/JSP000554Complete.lean) proves `lower_add_gap`, then both directions of `badGap_iff_exceptional` using actual consecutive primes, including the no-interior-prime condition. It identifies the good-index complement with existence of a rough interior witness. The density-zero/density-one and literal prefix-ratio limits are transported from the full Erdős 682 development; `exceptional_iff_residue` attaches our uniform finite classification to the same indexed prime gaps.

The complete target is the **almost-all-gaps** assertion, not an assertion that every consecutive prime pair has the witness. The initial gap 2→3 is handled in the index bridge; residue statements retain h ≥ 2. `jsp_000554` combines the credited analytic result with our uniform residue equivalence. A finite residue classification is not being offered as the analytic density proof.

Mathematical credit remains with Gafni–Tao, [*Rough numbers between consecutive primes*](https://arxiv.org/abs/2508.06463), and the sources they cite. The 51-module imported proof retains Codex/GPT-5.6 Sol and other source credits. Our review reproduces the root port including its explicit modification notice, so that notice is covered by the checksum rather than omitted.

## JSP-000585

All seven original modules—Certificate, GraphCore, Profile, Subdivision, Colouring, Catlin and Sharp—remain byte-identical to `019467ead20f2d6b87e672a1dfef7d5b8886febf`. Their 37 public theorems include the concrete graph, coloring/path arguments, explicit K7 subdivision and exact subdivision threshold. The original package was a finite special case.

The new [subdivision-model bridge](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/JSP000585Bridge.lean) converts branch-set certificates and indexed embeddings in both directions. Reversed paths preserve their interiors; the proof also preserves avoidance of branch vertices and pairwise disjoint interiors. Thus the comparison does not change the graph property by weakening the subdivision definition.

In [the complete endpoint](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9661ef0f170e750b1ac2153b9017bad86044680c/projects/catlin-research/JSP000585Complete.lean), our finite witness has chi=8 and sigma=7. It proves H(15) ≥ 8/7 and the necessary constraint `C ≥ (8/7)*log(15)/sqrt(15)` on every valid uniform upper-bound constant. It does **not** assert H(15)=8/7 or determine the best universal C. The positive-denominator condition is proved before passing to ratios.

The general existence of C>0 with `chi(G)/sigma(G) ≤ C*sqrt(n)/log(n)` for every n≥2 comes from the attributed Erdős 717 full proof, based on Fox–Lee–Sudakov, [Theorem 1.1](https://arxiv.org/pdf/1107.1920). Our finite Catlin witness supplies lower constraints, not the general upper proof. The imported 56 modules retain Codex/GPT-5.6 Sol and the Aharoni–Berger linkage credits; Catlin retains mathematical credit for the classical finite counterexample.

## JSP-000907

The earlier research note is retained byte-for-byte from `bd9e587d1411903124531f14329d8df98b076692`, with SHA-256 `584f4a2c9687de0b5484708ce2be7f71affadd588e247fee0d6deaec7b603a14`. This historical binding is evidence of the earlier note, not certification of every claim in it.

Our [Mathlib-only hub-and-diamond construction](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/555ce4f13bf7e8e8557020728f7f97ad3d1f51e0/projects/jsp-000907/JSP000907Construction.lean) proves the color-forcing equivalence and a four-color upper bound for suitable bases. [The odd-rim family](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/555ce4f13bf7e8e8557020728f7f97ad3d1f51e0/projects/jsp-000907/JSP000907OddRim.lean) has 8m+13 vertices and chromatic number four for every m; it uses the credited greedy-degree coloring lemma for the base cycle. [The witness module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/555ce4f13bf7e8e8557020728f7f97ad3d1f51e0/projects/jsp-000907/JSP000907Witness.lean) supplies a nine-cycle with at least four distinct chords for every member.

Our [complete integration](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/555ce4f13bf7e8e8557020728f7f97ad3d1f51e0/projects/jsp-000907/JSP000907Complete.lean) proves the equivalence of induced local hypotheses and **all** small subgraphs, including edge deletions. `explicit_counterexample` chooses m=floor(r/20), giving r<n≤r+31. `realGuarantee_le_ten` bounds every valid real threshold pointwise by ten without monotonicity, yielding bounded-range and no-divergence consequences.

The affirmative two-chord theorem retains its K4-free hypothesis. It comes from the credited Voss development. The full negative theorem uses the imported APSSV **ten-chord** family, not our odd-rim family. Our nine-cycle's four present chords prove neither a universal four-chord cap nor criticality; those stronger statements in the old note remain outside the formalized scope. `complete_package` appends our verified family to the complete two-part result without using those unproved note claims.

The 38-module imported closure retains OpenAI Codex, Brian Rabern/Opus 5 and other source credits. The mathematics is attributed to Voss and Alexeev–Putterman–Sawhney–Sellke–Valiant, [*Short proofs in combinatorics, probability and number theory II*](https://arxiv.org/abs/2604.06609), Section 4.

## Existing complete verification receipts

| Problem | Full source modules including audit | Axiom reports | Strict NaNoda declarations | Public run |
| --- | ---: | ---: | ---: | --- |
| 388 | 158 | 18 | 70,658 | [35295466997](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35295466997) |
| 725 | 46 | 28 | 33,087 | [35308272360](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35308272360) |
| 140 | 24 | 46 | 56,007 | [35347120839](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35347120839) |
| 554 | 54 | 37 | 76,193 | [35367960914](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35367960914) |
| 585 | 66 | 61 | 48,436 | [35332110641](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35332110641) |
| 907 | 43 | 35 | 19,125 | [35389263216](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35389263216) |

301's new targeted verification is described above. All these runs are contributor-operated automated checks using the pinned Lean/Mathlib environment. Cached Mathlib is not presented as a rebuild of all dependencies or an official isolated offline verification. API-reported artifact digests in the two new receipts are distinguished from the source hashes actually recomputed by the comparator.

Reviewers still need to assess statement fidelity, the value and eligibility of the additional formalization work, attribution and competing submissions. Successful checks and repository ownership do not constitute organizer acceptance, a first-formalization ruling or guaranteed payment.
