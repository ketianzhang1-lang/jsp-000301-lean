# JSP-000907: complete original statement and our odd-rim formalization

The endpoint `JSP000907.jsp_000907` in `JSP000907Complete.lean` proves both
questions of JSP-000907 / Erdős 1091:

1. Every finite four-chromatic, K4-free graph contains an odd cycle with at
   least two chords.
2. There is no real-valued function tending to infinity whose value at r is
   guaranteed as an odd-cycle chord count merely from three-colorability of
   every subgraph on at most r vertices.

The complete original result uses the attributed upstream formalization of
Voss's affirmative theorem and the Alexeev–Putterman–Sawhney–Sellke–Valiant
(APSSV) bounded-chord family. We add precise subgraph and real-threshold
bridges, a pointwise bound on every proposed guarantee, and an explicit
counterexample order r < n <= r+31. The latter is an arithmetic
reparameterization of the imported family, not a new mathematical construction.

Our independent color-forcing construction is in `JSP000907Construction.lean`.
For an arbitrary base graph, its three-colorability is equivalent to the
base graph's two-colorability. For every odd rim length 2m+3, we prove that
our graph has 8m+13 vertices and chromatic number exactly four. We also
construct a nine-cycle with four distinct chords for every m.
`JSP000907.complete_package` combines these results with the full original
problem. The four local proof files have 29 public theorems.

The stronger assertion in our earlier informal note—that every odd cycle
of our family has at most four chords—is **not** claimed as a Lean theorem
here. Its criticality and five-chord all-cycle cap also remain informal in
that note. The complete negative answer uses APSSV's fully formalized
ten-chord cap instead. No unproved claim from the earlier note is imported
as a premise. The original note remains unchanged at
`../../research-notes/jsp-000907/proof.md`.

## Reproduce

```sh
git clone --branch jsp-000907-complete-kz https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
# Check out the exact 40-character proof commit named in the catalog/PR.
cd projects/jsp-000907
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Git, Python 3, Lean/Lake, Rust/Cargo and network access are required. Lean
4.34.0 and all nine dependency revisions are pinned. The bootstrap script
fetches 38 source modules from one immutable upstream commit, checks their
original hashes, applies only the recorded compatibility changes and checks
the resulting hashes. Source headers and license notices are retained.

The verifier compiles all 43 modules with warnings treated as errors,
audits the 29 local and six upstream theorem closures, replays all proof
modules through Lean's checker, verifies dependency pins and rejects a
false arithmetic control. NaNoda separately checks the exported closures
with a hard allowlist of `propext`, `Classical.choice` and `Quot.sound`.
`VERIFICATION.md` records actual results; a configured check is not a claim
that the check already passed.

See `PROVENANCE.md` and `STATEMENT_FIDELITY.md` for contribution boundaries,
source credits and exact quantifiers. We request review of our construction,
statement bridges, compatibility integration and verification work, with no
claim of first-formalization priority or ownership of the imported proof.
