# Review supplement: JSP-000465, JSP-000897, JSP-000746 and JSP-001021

Prepared on 2026-09-19 for the existing Lean-only applications of
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance.
This supplement records source lineage, the exact contribution boundary,
supplementary finite computations and the correct verification versions.
It adds review evidence without changing the selected Lean proofs.

| Problem | Existing PR | Existing claim | Proof branch | Selected proof commit |
| --- | --- | --- | --- | --- |
| 465 | [#442](https://github.com/TheJustinSunPrize/awards/pull/442) | [#1572](https://github.com/TheJustinSunPrize/awards/issues/1572) | `jsp-000465-verified-kz` | `6a793b157c1afdf29f3e6bbbf3cf514535d1dfca` |
| 897 | [#439](https://github.com/TheJustinSunPrize/awards/pull/439) | [#1573](https://github.com/TheJustinSunPrize/awards/issues/1573) | `jsp-000897-dense-neighborhood-kz` | `914c6fa28200985d6409b5b34588b9f5c4a87d00` |
| 746 | [#402](https://github.com/TheJustinSunPrize/awards/pull/402) | [#1468](https://github.com/TheJustinSunPrize/awards/issues/1468) | `jsp-000746-sharp-kz` | `4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a` |
| 1021 | [#699](https://github.com/TheJustinSunPrize/awards/pull/699) | [#1586](https://github.com/TheJustinSunPrize/awards/issues/1586) | `jsp-001021-tournament-verification` | `7642a7f5eb190da6319b6ae7f11c829d7737e2dd` |

All four projects live in [our multi-problem repository](https://github.com/ketianzhang1-lang/jsp-000301-lean), under
`projects/jsp-000465`, `projects/jsp-000897`,
`projects/jsp-000746-sharp` and `projects/jsp-001021`, respectively.
The repository's original 301 name is not the problem identifier of these projects.

## JSP-000465

Our [interface module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/6a793b157c1afdf29f3e6bbbf3cf514535d1dfca/projects/jsp-000465/JSP000465.lean) proves the ordinary
singleton extremal-number equivalence, attainment by an actual family-free
graph, simultaneous strict separation and the direct negation of the universal
compactness assertion.

The quantifier order matters: **one fixed nonempty finite family** works for
every positive factor `K`; for each such factor, a common eventual threshold
works for **every member** of the family. The source first combines the
memberwise lower estimates with `eventually_all_finset`, then compares them
with the imported family little-o estimate. Its final counterexample retains
connectedness, bipartiteness and a cycle in every forbidden member.
The attainment lemma rules out interpreting the family extremum as a default
value of an empty feasible class.

The substantive quantitative construction is imported. In
[Ten Advances, Chapter 10, Theorem 1.1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=241)
(printed page 237), the counterexample has the stated connected, bipartite,
cyclic conditions. The introductory discussion distinguishes the corrected
cyclic version from the elementary forest example.
The `Erdos180` module name is the upstream organizational label; the inspected
counterexample supplies the stronger compactness obstruction needed for the
JSP-000465 / Erdős 575 submission.

**New reproducible evidence:** all seven imported modules match their original
upstream checksum manifest, and applying the published
[PORT.patch](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/6a793b157c1afdf29f3e6bbbf3cf514535d1dfca/projects/jsp-000465/PORT.patch) with zero fuzz reproduces all seven
selected modules exactly. The port changes three API call sites in two modules.
Our interface file is byte-identical to the file preserved in the
[initial submission commit](https://github.com/ketianzhang1-lang/awards/blob/90a8714f2f036112f39f0c7bb136c3b8751553b4/docs/submissions/jsp-000465-kz/proof/JSP000465.lean)
and the later documentation revision.

OpenAI/Astra retain credit for the quantitative proof.
[PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) registered existing
source before our submission. [PR #401](https://github.com/TheJustinSunPrize/awards/pull/401)
expressly concerns a forest example for the unrestricted formulation, rather
than the cyclic connected-bipartite theorem. This is a scope distinction,
not a claim that we originated the stronger construction.
Our requested contribution is the documented interface, consequences, port and
verification package; see [PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/cafcabe4fbd5c0f5b6c34d7162f35d4881c58925/projects/jsp-000465/PROVENANCE.md).

## JSP-000897

Our [four-theorem supplement](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/914c6fa28200985d6409b5b34588b9f5c4a87d00/projects/jsp-000897/JSP000897.lean) retains an explicit
integral surplus `s` in every maximum-degree vertex's neighborhood:
from `ex(n,K_r)+s ≤ e(G)`, it derives
`ex(d(v),K_(r-1))+s ≤ e(N(v))`.
The proof combines the credited `maximumDegree_edge_bound` and
`cliqueExtremal_split_le` with natural-number arithmetic.

The complete existence endpoint obtains a maximum-degree vertex and its
`n ≤ 2*d(v)` bound from the upstream threshold theorem, then invokes our
surplus lemma with `s = e(G)-ex(n,K_r)`.
The threshold assumption prevents truncated natural subtraction from weakening
the asserted surplus. The difference inequality is an equivalent consequence;
the strict result uses `s=1`. The public existence theorem retains
`r ≥ 4` and `n ≥ 2`.

**New reproducible evidence:** the retained original `upstream/Erdos1079.lean`
is byte-identical to the immutable upstream source.
The verifier reconstructs the selected port from that source using exactly the
documented import removals, renamed APIs and explicit Turán-number induction
target. Our supplement is unchanged in the
[initial submission history](https://github.com/ketianzhang1-lang/awards/blob/f8c1861271c900fdb8015ffb1abb06ed1562b068/docs/submissions/jsp-000897-kz/JSP000897.lean)
and later documentation revision.

These are useful explicit formal consequences of an existing argument, not
new mathematical discovery. Bollobás, Thomason and Bondy retain the mathematical
credit, and the upstream Codex / GPT-5.6 Sol attribution remains intact.
[PR #155](https://github.com/TheJustinSunPrize/awards/pull/155) predates ours.
The later [PR #1187](https://github.com/TheJustinSunPrize/awards/pull/1187)
expressly records an attributed threshold proof without claiming its authorship.
Neither an earlier catalog timestamp nor packaging alone establishes ownership
of that common dependency. See [PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9270ec89da6567daaa899d98bc95546073326c7d/projects/jsp-000897/PROVENANCE.md).

## JSP-000746

Our [finite supplement](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a/projects/jsp-000746-sharp/JSP000746Sharp.lean) gives a concrete
17-vertex graph, restricts it to every smaller initial interval, and combines
that obstruction with the attributed upper theorem to prove
`Forcing n ↔ 18 ≤ n` for every natural `n`.
Our [integer transport](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a/projects/jsp-000746-sharp/JSP000746.lean) uses the embedding
`i ↦ i+1` from `Fin 18` into the actual integers. Its endpoint gives positive
`a < b`, `a+b ≤ 18`, all three nonadjacencies and all distinctness conditions.

The sharpness witness supplies the lower direction of the finite equivalence.
The integer-graph existence proof uses the imported eighteen-point upper bound
and our transport; it does not require our seventeen-point lower witness.
This separates the roles of the two contributions.

**New finite check:** the supplementary Python verifier reads the literal edge
list from the selected Lean source and independently confirms **43 distinct
unoriented edges**, no triangle, and coverage of all **64** positive,
distinct-summand Schur triples in the interval 1 through 17.
These computations corroborate the selected witness; Lean's existing
`no_triangles` and `schur_coverage` proofs remain the formal evidence.

**Verification repair:** the catalog previously linked an earlier receipt.
The correct later NaNoda run is
[35302256694](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302256694) at
`d38c1169bbea335d1683589ba2bda3cf78c1b932`.
Both local proof modules, `UPSTREAM.json` and the dependency manifest are
byte-identical to the selected proof version. The
[updated receipt](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/f606b97bf0bad47b288cf2c9d97c044f0a3d9730/projects/jsp-000746-sharp/VERIFICATION.md)
and its machine-readable companion describe that later execution.
The selected proof commit remains unchanged.

Ben Barber retains mathematical credit for the upper bound, and the upstream
proof and SAT certificates retain their formal authorship. Earlier complete
work includes [PR #165](https://github.com/TheJustinSunPrize/awards/pull/165).
The later [PR #1156](https://github.com/TheJustinSunPrize/awards/pull/1156)
cites our #402 among pre-existing submissions and proposes a forty-edge optimum.
We have not independently certified that later full package. Our own
**43-edge witness is not claimed to minimize the edge count**; our exact
threshold concerns the number of vertices. See
[PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a/projects/jsp-000746-sharp/PROVENANCE.md).

## JSP-001021

The original [Erdős–Moser 1964 paper](https://real.mtak.hu/189065/1/cut_MATKUTINT_1964_1_-_2_pp125_-_132.pdf#page=3),
Section 1, printed page 127, expressly presents
`f(n)=floor(log₂ n)+1` and asks about `f(15)=4`.
This primary statement supports interpreting the submitted endpoint as a
complete disproof of that universal equality.

Our [main module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7642a7f5eb190da6319b6ae7f11c829d7737e2dd/projects/jsp-001021/JSP001021.lean) explicitly encodes restriction
to fourteen vertices and proves preservation of orientations, including the
reversed-order case. It transports the credited fourteen-vertex theorem to
every order at least fourteen, then proves `f(15) ≥ 5` and contradicts
`Nat.log2 15 + 1 = 4`.
The transport checks every required forward arc of the injected transitive
five-set. It is not merely a directed-path assertion.

Our [FiniteChecks.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7642a7f5eb190da6319b6ae7f11c829d7737e2dd/projects/jsp-001021/FiniteChecks.lean) is a **separate local
certificate supplement** to an earlier independent reconstruction.
It is imported but is not invoked by the complete disproof's theorem chain.
The main proof depends on the credited Reid–Parker fourteen-vertex theorem.
The certificate supplement does not establish that the entire independent
fifteen-vertex reconstruction has been formalized.

**New finite check:** the Python verifier reads the selected 196-entry witness
table and recomputes the local conditions. Of the 196 pairs, **126** satisfy
the intersection-size-one hypothesis: **84** have checked ordered transitive
five-set witnesses and **42** are retained patterns. The total retained count
is 42, and the final explicit five-set is also checked.
These figures clarify that the Lean local-exclusion theorem is conditional;
it does not assert 196 unconditional five-set witnesses.

**Verification repair:** the successful NaNoda run is
[35302257717](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302257717), at
`3ebcc72d98b50f59ff456feb5963f85815b2d09c`.
The main proof, finite-check source, upstream-source manifest and dependency
manifest are byte-identical to the selected proof.
The catalog should link the [updated receipt](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/6abe6a772ac84d1b24cceda0ba1bf4c27428b56e/projects/jsp-001021/VERIFICATION.md)
while keeping the original selected proof commit.

Reid–Parker retain mathematical credit and the reused Codex / GPT-5.6 Sol proof
retains formal credit. [PR #710](https://github.com/TheJustinSunPrize/awards/pull/710)
states that it found the prior fourteen-vertex source through #699.
The later [PR #1246](https://github.com/TheJustinSunPrize/awards/pull/1246)
acknowledges #699 among earlier complete submissions and proposes additional
exact-six results. These are bounded public acknowledgments, not proof of
global priority, organizer acceptance or ownership of the shared upstream proof.
Our early reproduction-only PR revision must not be treated as the publication
date of the later complete Lean endpoint.

## Reproduction and verification limits

[sources.json](sources.json) binds **45** immutable source snapshots by URL,
byte count, SHA-256 and Git blob hash. Run:

```bash
python3 verify_evidence.py
```

Python 3, GNU patch and network access are required. A prior download directory
can be supplied with `--source-cache DIR`.
[verify_evidence.py](verify_evidence.py) passed all documented comparisons and
finite computations during preparation.

The existing public workflows for 465
([35178564666](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178564666)) and 897
([35178602861](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178602861)) returned `success` at their
selected proof commits when queried on 2026-09-19. The 746 and 1021 workflows
above also returned `success` at their later verification commits.
Their proof projects retain the full build commands, locked dependencies and
axiom-audit records. This supplement is not a fresh Lean or NaNoda execution.

We request assessment of the complete submissions and the specifically
identified implementation, interface, integration and verification contributions.
Source hashes and successful computation support review but do not by
themselves establish independent authorship, first formalization, eligibility
or an award. Those decisions remain with the organizers.
