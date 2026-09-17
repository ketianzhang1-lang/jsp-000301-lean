# JSP-000017: known lonely-runner special cases

This is a Lean formalization of known special cases, prepared for review of a
possible formalization contribution. **It does not solve the general Lonely
Runner Conjecture.** The official catalog remains Open / Lean proof No /
Eligible to claim No. No change to these flags, new mathematics, first
formalization priority, award or payment entitlement is asserted.

## Exact scope

1. `JSP000017.three_runners`: for every injective real-valued speed assignment
   to `Fin 3`, and every chosen runner, there is a strictly positive time when
   its distance to each other runner in Mathlib's `UnitAddCircle` is at least
   `1/3`. Negative speeds and a stationary runner are allowed. No rationality
   or integrality assumption is imposed.
2. `JSP000017.doubling_runners`: for any total number `m+2` of runners, fix a
   reference runner. If the other runners can be listed so that their absolute
   relative velocities at least double at each step, a strictly positive
   common time achieves the exact threshold `1/(m+2)` against all of them.
   The ordering and doubling conditions are explicit hypotheses. This does
   not assert that all speed assignments satisfy them, or that their validity
   for one reference runner implies validity for every reference runner.
3. `three_runners_spec` uses the same user-supplied loneliness predicate,
   metric, and nonnegative-time conclusion as the existing Formal Conjectures
   three-runner specialization. `doubling_relative_to_runner` supplies the
   direct metric statement for a finite list. `doubling_speeds` and
   `doubling_real_speeds` are equivalent relative-velocity versions.

The module also contains interval-nesting lemmas and a stronger-ratio safe-band
construction for general separation thresholds. None is a computational
sample substituted for a universally quantified proof.

## Mathematical argument

A position is safe at threshold delta if it lies in some closed interval
`[z+delta, z+1-delta]`, where z is an integer. Such a position has circular
distance at least delta from zero. Signs of relative velocities do not change
this distance.

For two positive velocities `a <= b`, if `b <= 2a`, time `1/(3a)` works. If
`b > 2a`, the first runner stays safe throughout `[1/(3a), 2/(3a)]`; the second
runner travels at least `2/3` during this interval. Every real interval of
length `2/3` intersects a safe interval at threshold `1/3`. Translating to each
reference runner proves the three-runner case.

For the doubling family, an interval of positions of length at least
`2w+2delta` contains a safe subinterval of length w, provided
`0 <= w <= 1-2delta`. This follows by choosing the current or next integer
safe interval. Set `delta=1/(m+2)`. After including velocities `0,...,k`, retain
a common safe time interval whose length, multiplied by velocity k, is
`(m-k)delta`. Doubling the next velocity gives enough length for the next
selection. At `k=m` the retained interval may be a singleton but remains
nonempty and at a strictly positive time. Thus all required inequalities hold
at one time. Closed endpoints are essential and are preserved in Lean.

## Attribution and originality limits

The three-runner case is classical and elementary. The doubling-speed family
is a known result attributed to Javier Barajas and Oriol Serra in Theorem 18
of the survey by Guillem Perarnau and Oriol Serra,
[The Lonely Runner Conjecture turns 60](https://arxiv.org/abs/2409.20160),
especially Sections 6.1 and 7.3. The survey cites Barajas and Serra,
*On the chromatic number of circulant graphs*, Discrete Mathematics 309,
5687-5696. Mathematical credit remains with the prior literature.

The Lean proof in this directory was written for this submission with OpenAI
ChatGPT/Codex assistance. It uses an elementary nested-interval argument and
Mathlib's existing real arithmetic and quotient-circle metric infrastructure.
No external lonely-runner proof is imported. The interface of
`three_runners_spec` follows the statement in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/LonelyRunnerConjecture.lean).
The existing statement and its authors are not claimed as new contributions.
Verification scripts adapt the submitting account's earlier verification
pipeline. Searches found no official JSP-000017 filing at preparation time;
search coverage is not proof of global priority, and existing external
lonely-runner computation/formalization projects may overlap.

Proposed contributor placeholder: `RECIPIENT-JSP-000017-KZ-A`, confirmation
pending. This is a self-submission with a direct interest in the review outcome.

## Reproduction

Lean 4.34.0 and every package revision are pinned in `lean-toolchain` and
`lake-manifest.json`. Mathlib is commit
`5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The scripts build with warnings as errors, replay the built module with the
bundled Lean checker, audit eight declaration closures against the three
standard foundational axioms, reject a false-arithmetic negative control,
check actual dependency revisions, and run pinned NaNoda on the exported
dependency closures. NaNoda is configured to reject all non-allowlisted axioms,
including `sorryAx` and compiler-trust/native-evaluation axioms.

Verification logs and the tested source commit will be linked in the submission
receipt after the actual run. Contributor-run checks are not organizer approval
or independent human certification. Dependency caches and network access are
used; no offline full-library rebuild is claimed. GitHub Actions artifacts
have finite retention.

## License

The new proof and verification files are provided under the repository's MIT
license. Mathlib and other dependencies retain their own licenses and credits.
