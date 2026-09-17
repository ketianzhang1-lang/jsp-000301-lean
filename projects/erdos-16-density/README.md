# Erdős 16: natural-density statement alignment

This project completes the connection between a published Lean proof of Chen's one-progression theorem and the counting-limit statement of Erdős Problem 16. It also handles exponent zero. It is a formalization supplement, not a new mathematical discovery or a claim of first formalization of the problem.

Let `E` be the odd natural numbers that cannot be written as `p + 2^k`, with `p` prime and `k >= 0`. The final theorem proves that `E` is not the union of one infinite arithmetic progression and a set of natural density zero. Here density zero explicitly means

`lim_{n -> infinity} #{x < n : x in B} / n = 0`.

`Alignment.lean` checks the statement against the definition shape in the pinned Google DeepMind Formal Conjectures source. Neither its unproved theorem nor its `answer` mechanism is imported.

## Contribution

- A counting lower bound for an arithmetic progression.
- A proof that natural density zero implies absence of an infinite arithmetic progression.
- A proof that adding one point preserves absence of an infinite arithmetic progression.
- The exact identity between the positive-exponent and nonnegative-exponent exceptional sets: `U = insert 3 E`.
- Complete negative decomposition theorems for both exponent conventions, using the published proof as a prerequisite.

The upstream predicate called `density_zero` means absence of an infinite arithmetic progression, which is weaker than natural density zero. Its negative decomposition theorem is therefore stronger in this respect, once this implication is established. This supplement does not allege a false upstream theorem. It proves the missing definition bridge and the boundary conversion explicitly.

## Reproduce

Requires Lean 4.34.0, Python 3, Git, curl, and, for independent checking, Rust/Cargo.

```sh
python3 scripts/bootstrap.py
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The bootstrap downloads the unchanged upstream source at an immutable revision and checks SHA-256. It refuses mismatched existing files. The original source is not redistributed in this package.

See [STATEMENT.md](STATEMENT.md) for scope and proof, and [PROVENANCE.md](PROVENANCE.md) for sources and credits. Contributor-run verification is supporting evidence; it is not organizer approval or a payment entitlement. The independent checker scripts validate the actual exported dependency closures, with a hard error for axioms outside `propext`, `Classical.choice`, and `Quot.sound`.

## Prize status

No matching entry was located in the prize's 1,022-record catalog at `f4e7173d89dfe91022a185427d63452c8ffbf6ae`. No JSP identifier is assigned here. A problem recommendation and an assessment of this incremental contribution would be needed before any prize claim could be considered. The public rules do not establish that this supplement is prize-eligible.

This is the one-progression statement. It does not prove a result about unions of arbitrarily many progressions, Romanoff's positive-density theorem, or a new density estimate for the exceptional set.
