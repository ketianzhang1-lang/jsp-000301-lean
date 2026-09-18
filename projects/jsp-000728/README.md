# JSP-000728: our all-interval construction and complete original counting question

We contribute an independently written Lean proof of the Cameron–Erdős lower
bound for every interval, an exact bridge between two finite counting models,
and the formal relative-count conclusions of the original question. Our endpoint
is `JSP000728.jsp_000728` in [JSP000728Complete.lean](JSP000728Complete.lean).
We combine our construction with an attributed, fully pinned upper-bound proof;
the imported upper-bound argument is not our original contribution.

Write `M(N)` for the number of inclusion-maximal sum-free subsets of `{1,…,N}`
and `F(N)` for the number of all sum-free subsets. We establish:

- `2^floor(N/4) ≤ M(N)` for every natural `N`, including zero.
- `M(N) = o(2^(N/2))` and `M(N)/F(N) → 0`.
- There is a fixed real `δ > 0` such that, for all sufficiently large `N`,
  `M(N) ≤ F(N)/2^(δN)`.

The last statement supplies the exponential separation explicitly asked in the
original Cameron–Erdős question, as described in Section 1, page 2 of
[Balogh–Liu–Sharifzadeh–Treglown](https://arxiv.org/pdf/1409.5661).
The later sharp exponent `1/4` and residue-class asymptotic constants are not
proved here. [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md) explains the precise
original scope and the distinction from those stronger later results.

## Our contribution

| Component | What we prove |
| --- | --- |
| [JSP000728.lean](JSP000728.lean) | We formalize the odd-pair seed, its sum-freeness, maximal extension, incompatibility of different binary choices, and the all-`N` lower bound. This file is unchanged from our original proof revision. |
| [JSP000728Bridge.lean](JSP000728Bridge.lean) | We prove equality of the local and upstream maximal families and counts, including the reversed equality in their maximality predicates. We also construct the upper-half powerset injection and prove `F(N) ≥ 2^ceil(N/2) ≥ 2^(N/2)`. |
| [JSP000728Complete.lean](JSP000728Complete.lean) | We transport the verified upper bound into our finite model and derive both the vanishing ratio and the fixed exponential separation relative to all sum-free sets. |
| [Reproduction scripts](scripts) | We pin the complete 43-module upper-proof closure, record compatibility changes, audit the theorem dependencies and provide kernel replay and independent-checker instructions. |

For the lower construction, let `m = floor(N/4)`. When `m > 0`, we include `4m`
and one element from each pair `{2i+1, 4m-(2i+1)}` for `i < m`, then extend the
seed maximally. Distinct binary choices cannot have a common sum-free extension:
the opposite pair would sum to the included `4m`. For `m = 0`, we extend the
empty set. The local predicate permits equal summands and uses inclusion
maximality, not maximum cardinality.

## Reused mathematics and formal proof

The lower construction is due to Cameron and Erdős. The original exponential
separation was proved mathematically by Łuczak and Schoen; later sharper results
are due to Balogh, Liu, Sharifzadeh and Treglown. We claim no new informal theorem.

The full upper-bound Lean development is reused from
[plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos877.lean).
Its entry header credits formal work to Codex and GPT-5.6 Sol; the dependency
headers retain the Lean-Proofs Authors and OpenAI Codex notices. We preserve
those credits, [the upstream license notice](UPSTREAM-LICENSE.txt) and the
[Apache 2.0 license](APACHE-2.0.txt). Every fetched file and exact compatibility
edit is fixed in [UPSTREAM.json](UPSTREAM.json). See
[PROVENANCE.md](PROVENANCE.md) for the contribution boundaries and prior work.

## Reproduction

Lean **4.34.0**, Mathlib **5ed2965256430c3649e86755f9576b54eca72435**, and the
committed `lake-manifest.json` fix the environment. From a fresh checkout:

```sh
cd projects/jsp-000728
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The bootstrap fetches immutable source files and rejects checksum differences;
it never imports prebuilt upstream proof objects. The verifier compiles all
47 modules, audits 27 theorem closures, checks the nine actual dependency
revisions, replays all 43 upstream modules and our three proof modules, and
requires a false arithmetic statement to fail. NaNoda additionally requires
Rust/Cargo and checks the exported dependency closures with a strict axiom
allowlist. The public workflow provides that environment.

[VERIFICATION.md](VERIFICATION.md) records checks actually executed and their
limits. A workflow definition alone is not a passing result; select the run
whose `head_sha` matches the proof commit in the catalog or PR.

We prepared our formalization with OpenAI ChatGPT/Codex assistance under GitHub
account `ketianzhang1-lang`. We request review of our specific contributions,
not credit for the imported upper proof. This is not a claim of first
formalization, organizer approval or award entitlement. We update the existing
[PR #373](https://github.com/TheJustinSunPrize/awards/pull/373).
