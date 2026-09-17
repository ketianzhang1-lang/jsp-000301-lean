/-
Copyright 2026. Licensed under the Apache License, Version 2.0.

Independent Lean implementation prepared with OpenAI ChatGPT assistance.
The known factorial bound is credited to Jean-Marie Monier (1985).
The definition of `n` is adapted from The Formal Conjectures Authors (2026),
FormalConjectures/ErdosProblems/1063.lean, under Apache 2.0.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

open Finset

namespace JSP000883

/-- Exactly one of the k descending factors fails to divide the binomial coefficient. -/
def Admissible (k N : ℕ) : Prop :=
  2 * k ≤ N ∧ ∃ i0 < k, ¬ (N - i0) ∣ N.choose k ∧
    ∀ i < k, i ≠ i0 → (N - i) ∣ N.choose k

/-- The original least-starting-point definition. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

lemma descFactorial_mod {N K r : ℕ} (hKN : K ∣ N) (hr : r < N) :
    ((N - 1).descFactorial r : ZMod K) = (-1) ^ r * (r.factorial : ZMod K) := by
  have hN : (N : ZMod K) = 0 := (CharP.cast_eq_zero_iff (ZMod K) K N).mpr hKN
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub (by omega : r ≤ N - 1),
      Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one, hN,
      ih (by omega), pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    ring

lemma choose_multiple_factorial (a k : ℕ) (ha : 0 < a) :
    (a * (k + 1).factorial).choose (k + 1) =
      a * (a * (k + 1).factorial - 1).descFactorial k := by
  have hpos : 0 < a * (k + 1).factorial := Nat.mul_pos ha (Nat.factorial_pos _)
  have h := Nat.succ_descFactorial_succ (a * (k + 1).factorial - 1) k
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a * (k + 1).factorial),
    Nat.descFactorial_eq_factorial_mul_choose] at h
  apply Nat.mul_left_cancel (Nat.factorial_pos (k + 1))
  calc
    (k + 1).factorial * (a * (k + 1).factorial).choose (k + 1) =
        (a * (k + 1).factorial) * (a * (k + 1).factorial - 1).descFactorial k := h
    _ = (k + 1).factorial * (a * (a * (k + 1).factorial - 1).descFactorial k) := by ring

lemma self_not_dvd_choose_multiple_factorial (a k : ℕ) (ha : 0 < a) (hk : 1 ≤ k) :
    ¬ (a * (k + 1).factorial) ∣ (a * (k + 1).factorial).choose (k + 1) := by
  rw [choose_multiple_factorial a k ha, Nat.mul_dvd_mul_iff_left ha]
  intro hd
  have hlt : k < a * (k + 1).factorial := by
    have h1 := Nat.self_le_factorial (k + 1)
    have h2 : (k + 1).factorial ≤ a * (k + 1).factorial := by
      simpa using Nat.mul_le_mul_right (k + 1).factorial ha
    omega
  have hmod := descFactorial_mod (N := a * (k + 1).factorial)
    (K := (k + 1).factorial) (r := k) (dvd_mul_left _ _) hlt
  have hz : ((a * (k + 1).factorial - 1).descFactorial k : ZMod (k + 1).factorial) = 0 :=
    (CharP.cast_eq_zero_iff _ _ _).mpr hd
  have hzfac : (k.factorial : ZMod (k + 1).factorial) = 0 :=
    ((isUnit_neg_one.pow k).mul_right_eq_zero).mp (hmod.symm.trans hz)
  have hd' : (k + 1).factorial ∣ k.factorial := (CharP.cast_eq_zero_iff _ _ _).mp hzfac
  have hle := Nat.le_of_dvd (Nat.factorial_pos k) hd'
  have hpos := Nat.factorial_pos k
  rw [Nat.factorial_succ] at hle
  nlinarith

lemma all_other_factors_dvd (a k i : ℕ) (ha : 0 < a)
    (hi : i < k + 1) (hi0 : i ≠ 0) :
    (a * (k + 1).factorial - i) ∣ (a * (k + 1).factorial).choose (k + 1) := by
  rw [choose_multiple_factorial a k ha]
  apply dvd_mul_of_dvd_right
  rw [Nat.descFactorial_eq_prod_range]
  have hmem : i - 1 ∈ range k := by simp only [mem_range]; omega
  have hd := dvd_prod_of_mem (fun j => a * (k + 1).factorial - 1 - j) hmem
  have heq : a * (k + 1).factorial - 1 - (i - 1) = a * (k + 1).factorial - i := by
    omega
  simpa only [heq] using hd

lemma twice_le_factorial {k : ℕ} (hk : 3 ≤ k) : 2 * k ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    nlinarith

/-- Every positive multiple of k! is an explicit admissible starting point, for k ≥ 3. -/
theorem factorial_multiple_admissible {a k : ℕ} (ha : 0 < a) (hk : 3 ≤ k) :
    Admissible k (a * k.factorial) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨?_, 0, by omega, ?_, ?_⟩
  · have h1 := twice_le_factorial hk
    have h2 : (r + 1).factorial ≤ a * (r + 1).factorial := by
      simpa using Nat.mul_le_mul_right (r + 1).factorial ha
    exact h1.trans h2
  · simpa using self_not_dvd_choose_multiple_factorial a r ha (by omega)
  · exact fun i hi hi0 => all_other_factors_dvd a r i ha hi hi0

/-- Monier's known factorial upper bound, with the original least-element definition. -/
theorem monier_upper_bound {k : ℕ} (hk : 3 ≤ k) : n k ≤ k.factorial := by
  apply Nat.sInf_le
  simpa [Admissible] using (factorial_multiple_admissible (a := 1) (by decide) hk)

/-- Nonemptiness ensures that the infimum is an actual admissible starting point. -/
theorem least_is_admissible {k : ℕ} (hk : 3 ≤ k) : Admissible k (n k) := by
  exact Nat.sInf_mem (s := {N | Admissible k N}) ⟨k.factorial, by
    simpa using (factorial_multiple_admissible (a := 1) (by decide) hk)⟩

theorem least_bounds {k : ℕ} (hk : 3 ≤ k) : 2 * k ≤ n k ∧ n k ≤ k.factorial :=
  ⟨(least_is_admissible hk).1, monier_upper_bound hk⟩

/-- The explicit starting points form an infinite set, for every k ≥ 3. -/
theorem infinitely_many_starting_points {k : ℕ} (hk : 3 ≤ k) :
    {N : ℕ | Admissible k N}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun a : ℕ => (a + 1) * k.factorial)
  · intro a b h
    have := Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) h
    omega
  · exact fun a => factorial_multiple_admissible (Nat.succ_pos a) hk

end JSP000883
