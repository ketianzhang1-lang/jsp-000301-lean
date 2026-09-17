# JSP-000883 / Erdos 1063: Monier's factorial bound

This project formalizes a known component of JSP-000883. For every integer
`k >= 3`, the least `N >= 2*k` such that exactly one of
`N, N-1, ..., N-k+1` fails to divide `choose(N,k)` satisfies

```text
2*k <= n(k) <= k!.
```

More explicitly, **every positive multiple `N = a*k!` works**, and the unique
exception is `N` itself. Therefore there are infinitely many admissible
starting points for every `k >= 3`.

## Scope

The factorial bound is the known result attributed to **Jean-Marie Monier
(1985)** in the original statement. This project does not prove Cambie's
stronger least-common-multiple bound, improve that bound, determine all
admissible starting points, or solve the entire open problem. The infinite
family is an extension of the elementary argument; no new-mathematics or
worldwide first-formalization claim is made.

The least-starting-point definition is copied from the pinned Formal
Conjectures source. Its defining set is proved nonempty, and its infimum is
proved to belong to that set. Thus the bound does not rely on a default value
for the infimum of an empty set.

## Elementary proof

Fix `k >= 3`, `a >= 1`, and put `N = a*k!`. The factorial formula gives

```text
choose(N,k) = a * product_{i=1}^{k-1} (N-i).
```

Each factor `N-i` for `1 <= i < k` therefore divides `choose(N,k)`.
If `N` also divided it, cancellation of the positive factor `a` would imply
that `k!` divides the product on the right. However, modulo `k!`,

```text
product_{i=1}^{k-1} (N-i) = (-1)^(k-1) * (k-1)!.
```

Since `0 < (k-1)! < k!`, this is impossible. Also `N >= k! >= 2*k`.
Taking `a=1` proves the bound. Varying the positive integer `a` gives distinct
admissible starting points. The Lean proof implements the congruence in
`ZMod (k!)` and uses the invertibility of `(-1)^(k-1)`; it does not assume
that this residue ring is a field.

## Files and reproduction

- `JSP000883.lean`: product identity, modular obstruction, explicit family,
  least-element attainment, two-sided bounds and infinitude.
- `Compatibility.lean`: the exact upstream definition and the known Monier
  theorem type, applied by definitional equality. No unproved source theorem
  is imported.
- `Audit.lean`: nine target axiom audits.
- `scripts/verify.sh`: warning-free build, bundled kernel replay, dependency
  revision checks, axiom allowlist and a false-arithmetic negative control.
- `scripts/verify_nanoda.sh`: pinned exporter and independently implemented
  NaNoda checker with a strict three-axiom allowlist.

Use Lean 4.34.0 and the checked-in Mathlib dependency lockfile:

```sh
lake exe cache get Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Factorial.BigOperators Mathlib.Data.ZMod.Basic Mathlib.Order.ConditionallyCompleteLattice.Basic Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

These commands describe the verification procedure. Actual successful runs
and immutable source pins must be cited separately in the submission receipt.
Bundled `leanchecker` uses Lean's kernel implementation. NaNoda is a separate
checker. Official compiled Mathlib caches are used; no whole-library rebuild
or independent human certification is claimed.

## Sources and attribution

- [Original problem](https://www.erdosproblems.com/1063).
- [Pinned original statement and bibliography](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean).
- Jean-Marie Monier, *Problems and Solutions: Solutions of Advanced Problems:
  6447*, American Mathematical Monthly 92 (1985), 435-436.
- Paul Erdos and John L. Selfridge, *Problem 6447*, American Mathematical
  Monthly (1983), 710.
- Richard K. Guy, *Unsolved Problems in Number Theory* (2004), Problem B31.

The definition and compatibility theorem type are adapted from **The Formal
Conjectures Authors (2026)** under Apache 2.0. Mathematical credit for the
factorial bound remains with Monier. This proof implementation was written
independently with **OpenAI ChatGPT assistance** under the submitting account's
direction. Mathlib infrastructure is acknowledged. See `LICENSE`.

At the selection check on 2026-09-17, searches of the official repository for
`JSP-000883`, `1063`, and `Monier` returned no matching contribution. The
checked public plby proof-tree snapshot had no `Erdos1063` file. These are
limited overlap checks, not proof of worldwide priority.
