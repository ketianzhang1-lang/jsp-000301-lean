# JSP-000506: joint gaps, conditional sampling and mean-gap extension

Prepared by `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance, on 2026-09-19.
This supplements [catalog PR #363](https://github.com/TheJustinSunPrize/awards/pull/363)
and the existing [award claim #1623](https://github.com/TheJustinSunPrize/awards/issues/1623).

## New formal contribution

The unchanged complete package proves the original random-graph statement.
Our new `JSP000506Selection.lean` adds **11 proved lemmas and theorems**,
including the finite-probability estimates supporting three extensions.
These statements are formal consequences of the credited quantitative theorem;
they are not claims of a newly discovered mathematical result or a new best scale.

Let D(G) = chi(G) - zeta(G), let Gbar be the complement of G on the same
labelled vertices, and write s(n) for the existing positive quantitative scale
C*n/(log n)^3. The natural subtraction in D is literal because zeta <= chi.
All probabilities use exact uniform counting on every simple labelled graph,
already identified with the standard G(n,1/2) model in our original bridges.

### 1. Simultaneous graph and complement gaps

`joint_gap_probability_bounds` proves, for every finite n and real a,b,

```text
P(D(G) >= a and D(Gbar) >= b) >= P(D(G) >= a) + P(D(G) >= b) - 1.
```

Complementation preserves the uniform graph law; **independence of G and
Gbar is neither true nor assumed**. `joint_quantitative_gap_tendsto_one`
proves that both gaps reach s(n) simultaneously with probability tending to
one along all n. `joint_threshold_tendsto_one` allows two different arbitrary,
possibly nonmonotone threshold functions eventually below s(n).

### 2. Arbitrary conditional sampling, with explicit hypotheses

`conditionalProbability A B` is the exact ratio P(A intersection B)/P(B).
Every theorem using it as a conditional law requires positive retained mass,
at least eventually. The finite bound `conditional_joint_failure_bounds` is

```text
P(not(both gaps >= t) | B) <= 2 * (1 - P(D(G) >= t)) / P(B),  provided P(B)>0.
```

`conditional_joint_gap_tendsto_one` allows any sets B(n) of labelled graphs,
including graph-dependent and rare selections, when

```text
(1 - P(D(G) >= f(n))) / P(B(n)) -> 0,  with P(B(n))>0 eventually.
```

`positive_mass_conditioning_tendsto_one` supplies a directly usable sufficient
condition: B(n) retains at least one fixed c>0 of all graphs eventually and
f(n)<=s(n) eventually. No independence, monotonicity or invariance assumption
is placed on B(n). This does **not** say that conditioning on any nonempty or
arbitrarily rare event preserves the conclusion; the mass/ratio hypotheses
cannot be omitted. No numerical failure rate or universal rarity threshold is claimed.

### 3. Expected smaller gap

`meanMinimumPairGap` is the exact uniform average of min(D(G),D(Gbar)).
`mean_minimum_pair_gap_lower` proves the finite tail bound

```text
E[min(D(G),D(Gbar))] >= t * P(both gaps >= t).
```

`mean_minimum_pair_gap_scale_lower` proves that for **each fixed c<1**,
the expectation is eventually at least c*s(n).
`mean_minimum_pair_gap_tendsto_atTop` therefore proves its divergence to
infinity along all graph orders. These are lower bounds, not an upper bound,
an asymptotic equality or an explicit computable order threshold.

The remaining supporting results are `intersection_probability_lower` and
`conditional_failure_bounds`, proved in the generic finite Boolean-cube model.

## Attribution and complete source

The complete quantitative theorem is Samuil Petkov's credited work, with
the mathematical and AI-assistance credits retained by the existing package.
Annika Heckel retains credit for the finite concentration reduction. All
upstream authors, Mathlib and Lean contributors retain their original credit.
Petkov's original CC BY 4.0 source is unchanged; our new file carries our
Apache 2.0 notice without relicensing any imported work. Our contribution here
is the specified finite bounds and graph-complement, conditional-law and
expectation consequences, together with their formal integration and checks.

- Repository: `https://github.com/ketianzhang1-lang/jsp-000301-lean`.
- Branch: `jsp-000506-selection-20260919`.
- Selected complete-package commit: `90e1298ec99973eefe607f9c21bfffa750804087`.
- New [proof module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/90e1298ec99973eefe607f9c21bfffa750804087/projects/jsp-000506/JSP000506Selection.lean).
- [Combined theorem audit](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/90e1298ec99973eefe607f9c21bfffa750804087/projects/jsp-000506/AuditSelection.lean).
- The original complete proof and all its checking inputs are retained from
  `2aca2f16eba715d7ad672dfa017481b647c00063`.

The verification script compares original Lean sources, original Python/shell
checking scripts, selected manifests, license and toolchain inputs against
that immutable original commit. Their hashes and the new checking inputs are
rechecked after verification. The supplement imports the original complete
endpoint and does not replace it with a partial statement.

## Executed verification

[Public run 35417036545](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35417036545) succeeded at the exact selected
source commit. It freshly compiled the unchanged complete source chain,
including the upstream release containing 480 embedded source modules,
then compiled the supplement with warnings treated as errors.
The original four module kernel replays and the new module replay passed.
All **60 combined axiom reports** passed with only `propext`,
`Classical.choice` and `Quot.sound` permitted. Both original and supplementary
false-arithmetic controls were rejected for the expected reason.

The separately implemented NaNoda checker checked **60,183
declarations with no errors** across those 60 target closures. Its configuration
uses the same three-axiom allowlist, `unpermitted_axiom_hard_error=true`, and
requires nonempty printed statements plus an explicit successful declaration
count. Exporter and checker revisions are pinned in the script.

[SELECTION_RECEIPT.json](SELECTION_RECEIPT.json) records the run, job, source
and GitHub-reported artifact metadata. The source archive includes the
supplement and original package; the reconstructed unchanged upstream source
is included separately in the evidence artifact. The artifact has finite
retention, and its reported ZIP digest was not independently rehashed locally.

Reproduce from `projects/jsp-000506` at the selected commit:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
python3 scripts/verify_selection.py
bash scripts/verify_selection_nanoda.sh
```

The environment is Lean/Mathlib 4.31.0 with nine locked dependencies; the
scripts also require Python, Git, Rust/Cargo and network access. This verification
uses pinned cached Mathlib objects. It is not a fresh source rebuild of every
dependency, official offline verification, independent human semantic review,
first-formalization priority or a decision on award eligibility.
