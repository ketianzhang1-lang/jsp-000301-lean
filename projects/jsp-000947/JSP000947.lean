/-
Copyright 2026 Ketian Zhang. Licensed under Apache-2.0.
Prepared with OpenAI Codex.
The definition Good reproduces Erdos1142.Erdos1142Prop from Formal Conjectures,
commit 40e7c98697de6f66b8cbdbf641749ab39ed9c152 (copyright 2026 its authors).
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace JSP000947

def Good (n : ℕ) : Prop :=
  2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

def known : Finset ℕ := {4, 7, 15, 21, 45, 75, 105}

/-- A directly checked proper divisor of one required prime. -/
def bad (n p k : ℕ) : Bool :=
  decide (1 < p ∧ 0 < k ∧ 2 ^ k + p < n ∧ n % p = (2 ^ k) % p)

theorem not_good_of_bad {n p k : ℕ} (hb : bad n p k = true) : ¬ Good n := by
  simp only [bad, decide_eq_true_eq] at hb
  rintro ⟨_, hg⟩
  have hprime := hg k hb.2.1 (by omega)
  have hd : p ∣ n - 2 ^ k := Nat.ModEq.dvd' hb.2.2.2.symm
  rcases hprime.eq_one_or_self_of_dvd p hd with h | h <;> omega

/-- The table is untrusted input: each selected divisor is checked again by `bad`. -/
def sieve (rows : List (ℕ × Array ℕ)) (n : ℕ) : Bool :=
  rows.any fun row => bad n row.1 (row.2[n % row.1]!)

theorem not_good_of_sieve {rows : List (ℕ × Array ℕ)} {n : ℕ}
    (h : sieve rows n = true) : ¬ Good n := by
  obtain ⟨row, _, hb⟩ := List.any_eq_true.mp h
  exact not_good_of_bad hb

/-- Balanced enumeration avoids a linear-depth proof-reduction stack. -/
def checkTree (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, start => f start
  | depth + 1, start => checkTree f depth start && checkTree f depth (start + 2 ^ depth)

theorem checkTree_join {f : ℕ → Bool} (depth start : ℕ)
    (h₁ : checkTree f depth start = true)
    (h₂ : checkTree f depth (start + 2 ^ depth) = true) :
    checkTree f (depth + 1) start = true := by
  simp only [checkTree, h₁, h₂, Bool.and_self]

theorem checkTree_sound {f : ℕ → Bool} (depth start : ℕ)
    (hc : checkTree f depth start = true) :
    ∀ t, start ≤ t → t < start + 2 ^ depth → f t = true := by
  induction depth generalizing start with
  | zero =>
    intro t hlow hhigh
    have : t = start := by simp at hhigh; omega
    subst t
    exact hc
  | succ depth ih =>
    have hpair : checkTree f depth start = true ∧
        checkTree f depth (start + 2 ^ depth) = true := by
      simpa only [checkTree, Bool.and_eq_true] using hc
    intro t hlow hhigh
    by_cases ht : t < start + 2 ^ depth
    · exact ih start hpair.1 t hlow ht
    · apply ih (start + 2 ^ depth) hpair.2 t (by omega)
      simp only [pow_succ] at hhigh
      omega

def passes (rows : List (ℕ × Array ℕ)) (bound n : ℕ) : Bool :=
  decide (n ∈ known) || decide (bound < n) || sieve rows n

theorem passes_sound {rows : List (ℕ × Array ℕ)} {bound n : ℕ}
    (hp : passes rows bound n = true) (hn : n ≤ bound) (hg : Good n) : n ∈ known := by
  simp only [passes, Bool.or_eq_true, decide_eq_true_eq] at hp
  rcases hp with (h | h) | h
  · exact h
  · omega
  · exact (not_good_of_sieve h hg).elim

/-- A prime whose nonzero residues are small powers of two must divide a large solution. -/
theorem forced_divisor (p bound n : ℕ) (hp : 1 < p)
    (hcover : ∀ r, r < p → r ≠ 0 →
      ∃ k, 0 < k ∧ 2 ^ k + p ≤ bound ∧ (2 ^ k) % p = r)
    (hn : bound < n) (hg : Good n) : p ∣ n := by
  by_contra hnot
  have hr : n % p ≠ 0 := fun he => hnot (Nat.dvd_of_mod_eq_zero he)
  obtain ⟨k, hk, hsmall, he⟩ := hcover (n % p) (Nat.mod_lt n (by omega)) hr
  apply not_good_of_bad (n := n) (p := p) (k := k) _ hg
  simp only [bad, decide_eq_true_eq]
  exact ⟨hp, hk, by omega, he.symm⟩

end JSP000947
