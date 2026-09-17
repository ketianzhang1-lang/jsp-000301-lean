# JSP-000393: our sparse-square construction and complete minimum-support bounds

We provide a complete Lean endpoint for the original minimum-support question,
together with our explicit sparse-square construction and its consequences for
the same minimum function. We developed our implementation and integration under
GitHub account `ketianzhang1-lang` with OpenAI ChatGPT/Codex assistance.

Let `T(P)` be the number of nonzero coefficients of an ordinary polynomial and
let `f(n)` be the minimum of `T(P²)` over rational polynomials with exactly `n`
nonzero coefficients. The minimum is proved nonempty and attained for every `n`,
including zero. The development proves **`f(n) → ∞`**.

## Our contribution

We retain our independently implemented Coppersmith–Davenport construction:

- The explicit integer seed has `T(S) = 13` and `T(S²) = 12`.
- The recursively defined separated-exponent family has `T(F_k) = 13^k` and
  `T(F_k²) = 12^k` for every natural `k`.
- Our implementation proves the coefficient identities, noncancellation,
  separated-exponent multiplication and exact support counts inside Lean.

We add a proved coefficient-ring bridge and connect that construction to the
original minimum function:

- `rational_family_counts` preserves both exact counts under the integer-to-rational map.
- `minimum_family_upper_bound` proves **`f(13^k) ≤ 12^k`** for every `k`.
- `arbitrarily_large_small_ratio` proves that, for every `M` and every cutoff `N`,
  there is `n ≥ N` with **`M * f(n) < n`**. The small-ratio examples occur at
  arbitrarily large support sizes.
- `integer_schinzel_bound` and `integer_uniform_threshold` connect the general
  lower bound back to our integer-polynomial model.
- `jsp_000393` combines the full divergence theorem and our constructive
  consequences in one unconditional interface.

The exact theorem locations are `JSP000393.family_counts` and
`JSP000393.arbitrarily_sparse_squares` in [JSP000393.lean](JSP000393.lean), and
`JSP000393Complete.jsp_000393` with its supporting lemmas in
[JSP000393Complete.lean](JSP000393Complete.lean).

## Complete proof and attribution

Schinzel's general lower bound is supplied by the existing complete formalization
in [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos485.lean),
pinned at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its recorded formal authors
are **Codex and GPT-5.6 Sol**; mathematical credit belongs to **Andrzej Schinzel**.
The bootstrap fetches the full 22-module proof dependency chain and verifies
both the upstream and compatibility-port SHA-256 hashes. No missing theorem is
assumed as an axiom. The compatibility port updates deprecated conditional and monomial lemma
names and the multivariate coefficient-access interface in five files; the
mathematical assertions and proof arguments are retained.

Our sparse-square mathematics is credited to **Don Coppersmith and James H.
Davenport**, *Polynomials whose powers are sparse*, Acta Arithmetica 58 (1991),
79–87, especially the seed on p. 86 and product constructions on pp. 80–81.
[Primary paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa58/aa5816.pdf).
Schinzel's source is *On the number of terms of a power of a polynomial*, Acta
Arithmetica 49 (1987), 55–70,
[DOI](https://doi.org/10.4064/aa-49-1-55-70).

Our contribution is the separately implemented explicit construction, the new
bridges and consequences, and the verified integration. We do not claim an
independent proof of Schinzel's theorem, new mathematics, or first formalization
of the original problem. The earlier registration in
[issue #44](https://github.com/TheJustinSunPrize/awards/issues/44) remains credited.
See [PROVENANCE.md](PROVENANCE.md) and
[STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md) for exact boundaries.

## Reproduction

Check out the full proof commit identified in PR #368 on branch
`jsp-000393-sparse-squares`, then run at the repository root:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
python3 scripts/verify_complete.py
```

Lean is pinned to **4.34.0** and Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`; all transitive package revisions are
locked in `lake-manifest.json`. Keep that manifest when reproducing the proof.
The bootstrap requires network access to the immutable public source URLs.

The verifier fixes `LEAN_NUM_THREADS=1` for bounded-memory replay, compiles 25 modules with warnings as errors, checks all nine
package revisions, audits 13 target dependency closures against `propext`,
`Classical.choice`, and `Quot.sound`, replays the upstream module tree and both
our proof modules with Lean's bundled kernel checker, and rejects a false
arithmetic control. It writes actual execution logs and source hashes to
`evidence-complete/`. A workflow definition alone is not verification evidence;
see [VERIFICATION.md](VERIFICATION.md) for the executed checks.

These are contributor-run checks with cached dependencies. Lean's bundled
checker uses Lean's own kernel; this revision does not claim an independently
implemented checker replay of the complete integrated development. Maintainer
review of statement correspondence, contribution eligibility and any award
remains pending.
