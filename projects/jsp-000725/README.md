# JSP-000725: our interval construction and complete extremal statement

We contribute an independently written Lean formalization of the classical
interval construction, an exact bridge between natural-number and integer
formulations, and a complete endpoint showing that our explicit witness is
eventually optimal among all admissible sets. The endpoint is
`JSP000725.jsp_000725` in [JSP000725Complete.lean](JSP000725Complete.lean).

For a finite set `A ⊆ {1,…,N}`, admissibility means that two subsets with equal
sums have equal cardinalities. Let `M(N)` be the maximum cardinality over the
entire family of admissible sets. We establish:

- For every natural `N`, including zero, our terminal interval is admissible
  and has exactly `Nat.sqrt (4*N+1) - 1` elements.
- For all sufficiently large `N`, every admissible subset of `{1,…,N}` has
  at most that many elements. Thus our terminal interval attains the maximum.
- `M(N) = Nat.sqrt (4*N+1) - 1` eventually, and `M(N)/sqrt(N) → 2`.

Here `Nat.sqrt` is integer square root. The original question is Erdős problem
874. The eventual exact result is Theorem 1, page 142, of
[Deshouillers–Freiman (1999)](https://www.numdam.org/article/AST_1999__258__141_0.pdf).
We do not assert the exact maximum formula for every small `N`, or supply an
explicit numerical threshold. [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md)
records the definitions and quantifiers.

## Our contribution

| Component | Contribution |
| --- | --- |
| [JSP000725.lean](JSP000725.lean) | Our original ten theorems: subset-sum bounds, the general admissible interval construction, its exact cardinality, an all-`N` witness, the even-length family, and a boundary obstruction. This file is byte-identical to our original proof revision. |
| [JSP000725Bridge.lean](JSP000725Bridge.lean) | We prove the natural/integer predicate equivalence, preserve sums and cardinalities, include empty subsets correctly, and identify the actual finite extremal functions. |
| [JSP000725Complete.lean](JSP000725Complete.lean) | We use our original construction directly as the all-`N` witness and combine it with the attributed upper proof to establish eventual optimality, the exact maximum, and the limit. |
| [Reproduction scripts](scripts) | We pin all 42 upstream source modules and their compatibility edits, provide 28 theorem-closure audits, kernel replay, and a strict-allowlist NaNoda workflow. |

Our boundary obstruction proves that, for every `t ≥ 2`, the `2t`-element
interval `{t²−t,…,t²+t−1}` is inadmissible. This shows why the even-length
construction cannot uniformly lower its endpoint by one. The eventual
arbitrary-set upper bound comes from the separate imported development.

## Attribution and source boundary

The interval construction is classical work of Straus. The eventual exact
upper theorem is due to Deshouillers and Freiman. We claim formalization and
integration contributions, not a new mathematical solution.

We reuse the complete upper-proof closure from
[plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos874.lean).
Its entry credits Codex and GPT-5.6 Sol for formal work and retains the Boris
Alexeev copyright notice. We preserve the source headers,
[upstream license notice](UPSTREAM-LICENSE.txt), and [Apache 2.0 license](APACHE-2.0.txt).
[UPSTREAM.json](UPSTREAM.json) fixes all source bytes and exact port edits.
[PROVENANCE.md](PROVENANCE.md) distinguishes our work from the reused proof.
We do not claim authorship of that upper-bound development or first-formalization
priority.

We prepared our contributions under the submitting GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. Maintainers must
review these specific contributions and their eligibility; ownership or a
successful build alone does not establish an award claim.

## Reproduction

Use Lean **4.34.0**, Mathlib **5ed2965256430c3649e86755f9576b54eca72435**, and
the committed `lake-manifest.json`. From a fresh checkout:

```sh
cd projects/jsp-000725
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The bootstrap downloads immutable upstream source, checks original hashes,
applies only recorded compatibility changes, and checks final hashes. It does
not download prebuilt upper-proof objects. The verifier compiles all 46 modules,
audits 28 theorem closures, checks nine dependency revisions, replays every
upstream and local proof module, and requires a false-arithmetic control to fail.
NaNoda requires Rust/Cargo and checks all exported target dependency closures
with only `propext`, `Classical.choice`, and `Quot.sound` allowed.

Consult [VERIFICATION.md](VERIFICATION.md) for checks actually executed. A
workflow definition alone does not establish a passing run. This package updates
the existing [PR #361](https://github.com/TheJustinSunPrize/awards/pull/361).
