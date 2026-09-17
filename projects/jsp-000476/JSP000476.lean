/-
Copyright 2026. Released under the Apache License 2.0.
Independently written with OpenAI ChatGPT assistance.
The prime-multiple lower-bound construction is classical; see README.md.
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Squarefree

namespace JSP000476
open Finset

/-- Sum of the first m positive integers. -/
def triangle (m : ℕ) : ℕ := ∑ i ∈ range m, (i + 1)

/-- The first m positive multiples of p. -/
def multiples (p m : ℕ) : Finset ℕ := (range m).image (fun i => p * (i + 1))

/-- Every nonempty subset has a sum different from every square. -/
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ∀ x : ℕ, ∑ a ∈ S, a ≠ x ^ 2

/-- Every nonempty subset avoids all perfect powers with exponent at least two. -/
def PowerSumFree (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ∀ x k : ℕ, 2 ≤ k → ∑ a ∈ S, a ≠ x ^ k

theorem triangle_succ (m : ℕ) : triangle (m + 1) = triangle m + (m + 1) := by
  simp [triangle, sum_range_succ]

theorem triangle_double (m : ℕ) : 2 * triangle m = m * (m + 1) := by
  induction m with
  | zero => simp [triangle]
  | succ m ih => rw [triangle_succ]; nlinarith

theorem le_triangle (m : ℕ) : m ≤ triangle m := by
  have := triangle_double m
  nlinarith

theorem subset_sum_le_triangle {m : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) :
    (∑ i ∈ S, (i + 1)) ≤ triangle m := by
  exact sum_le_sum_of_subset hS

theorem all_sums_attained (m t : ℕ) (ht : t ≤ triangle m) :
    ∃ S ⊆ range m, ∑ i ∈ S, (i + 1) = t := by
  induction m generalizing t with
  | zero =>
      have : t = 0 := by simpa [triangle] using ht
      subst t
      exact ⟨∅, by simp, by simp⟩
  | succ m ih =>
      by_cases h : t ≤ triangle m
      · obtain ⟨S, hS, he⟩ := ih t h
        exact ⟨S, hS.trans (range_mono (by omega)), he⟩
      · have hm : m + 1 ≤ t := by have := le_triangle m; omega
        have hb : t - (m + 1) ≤ triangle m := by rw [triangle_succ] at ht; omega
        obtain ⟨S, hS, he⟩ := ih (t - (m + 1)) hb
        refine ⟨insert m S, ?_, ?_⟩
        · intro i hi
          rcases mem_insert.mp hi with rfl | hi
          · simp
          · exact range_mono (by omega) (hS hi)
        · have hn : m ∉ S := by intro hs; have := mem_range.mp (hS hs); omega
          rw [sum_insert hn, he]
          omega

theorem multiples_card {p : ℕ} (hp : 0 < p) (m : ℕ) : (multiples p m).card = m := by
  rw [multiples, card_image_of_injective]
  · exact card_range m
  · intro i j hij
    have := (Nat.mul_left_cancel hp hij)
    omega

theorem prime_mul_not_power {p t : ℕ} (hp : p.Prime) (ht : 0 < t) (hlt : t < p)
    (x k : ℕ) (hk : 2 ≤ k) : p * t ≠ x ^ k := by
  intro he
  have hpx : p ∣ x := hp.dvd_of_dvd_pow (he ▸ Nat.dvd_mul_right p t)
  have hsq : p ^ 2 ∣ x ^ k :=
    dvd_trans (pow_dvd_pow_of_dvd hpx 2) (pow_dvd_pow x hk)
  rw [← he, pow_two] at hsq
  have hpt : p ∣ t := Nat.dvd_of_mul_dvd_mul_left hp.pos hsq
  exact (not_le_of_gt hlt) (Nat.le_of_dvd ht hpt)

theorem multiples_power_free {p m : ℕ} (hp : p.Prime) (hm : triangle m < p) :
    PowerSumFree (multiples p m) := by
  intro S hS hn x k hk
  obtain ⟨T, hT, rfl⟩ := subset_image_iff.mp hS
  have hinj : Function.Injective (fun i : ℕ => p * (i + 1)) := by
    intro i j he
    have := Nat.mul_left_cancel hp.pos he
    omega
  rw [sum_image (fun i _ j _ he => hinj he), ← mul_sum]
  have hTn : T.Nonempty := image_nonempty.mp hn
  have ht : 0 < ∑ i ∈ T, (i + 1) := sum_pos (by intros; omega) hTn
  exact prime_mul_not_power hp ht ((subset_sum_le_triangle hT).trans_lt hm) x k hk

theorem power_free_square_free {A : Finset ℕ} (h : PowerSumFree A) : SquareSumFree A := by
  intro S hS hn x
  exact h S hS hn x 2 (by omega)

/-- Exact failure certificate: if the coefficient budget reaches p, a subset sums to p². -/
theorem multiples_square_witness {p m : ℕ} (hp : p.Prime) (hm : p ≤ triangle m) :
    ∃ S ⊆ multiples p m, S.Nonempty ∧ ∑ a ∈ S, a = p ^ 2 := by
  obtain ⟨T, hT, he⟩ := all_sums_attained m p hm
  have hinj : Function.Injective (fun i : ℕ => p * (i + 1)) := by
    intro i j hij
    have := Nat.mul_left_cancel hp.pos hij
    omega
  refine ⟨T.image (fun i => p * (i + 1)), image_subset_image hT, ?_, ?_⟩
  · apply image_nonempty.mpr
    by_contra hn
    have : T = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [this] at he
    exact hp.ne_zero he.symm
  · rw [sum_image (fun i _ j _ hij => hinj hij), ← mul_sum, he, pow_two]

/-- Sharp classification for this entire family, not just individual examples. -/
theorem multiples_square_free_iff {p : ℕ} (hp : p.Prime) (m : ℕ) :
    SquareSumFree (multiples p m) ↔ triangle m < p := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨S, hS, hne, he⟩ := multiples_square_witness hp (by omega : p ≤ triangle m)
    exact h S hS hne p he
  · intro hm
    exact power_free_square_free (multiples_power_free hp hm)

theorem multiples_power_free_iff {p : ℕ} (hp : p.Prime) (m : ℕ) :
    PowerSumFree (multiples p m) ↔ triangle m < p :=
  ⟨fun h => (multiples_square_free_iff hp m).mp (power_free_square_free h),
   multiples_power_free hp⟩

theorem exact_criterion {p : ℕ} (hp : p.Prime) (m : ℕ) :
    SquareSumFree (multiples p m) ↔ m * (m + 1) < 2 * p := by
  rw [multiples_square_free_iff hp m]
  have := triangle_double m
  omega

/-- A size-m construction avoiding every perfect power, in an explicit cubic interval. -/
theorem exists_power_free_card (m : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (m ^ 2 * (m + 1)) ∧ A.card = m ∧ PowerSumFree A := by
  by_cases hm : m = 0
  · subst m
    exact ⟨∅, by simp, by simp, by intro S hS hn; have := subset_empty.mp hS; simp_all⟩
  have ht : triangle m ≠ 0 := by have := le_triangle m; omega
  obtain ⟨p, hp, hplt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (triangle m) ht
  refine ⟨multiples p m, ?_, multiples_card hp.pos m, multiples_power_free hp hplt⟩
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  have him : i + 1 ≤ m := by have := mem_range.mp hi; omega
  apply mem_Icc.mpr
  constructor
  · exact Nat.mul_pos hp.pos (by omega)
  · calc
      p * (i + 1) ≤ (2 * triangle m) * m := Nat.mul_le_mul hple him
      _ = m ^ 2 * (m + 1) := by rw [triangle_double]; ring

/-- The same construction works in every larger interval. -/
theorem exists_power_free_in_interval (N m : ℕ) (hm : m ^ 2 * (m + 1) ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ A.card = m ∧ PowerSumFree A := by
  obtain ⟨A, hA, hc, hf⟩ := exists_power_free_card m
  exact ⟨A, hA.trans (Icc_subset_Icc (by omega) hm), hc, hf⟩

/-- An elementary uniform cube-root lower bound, stated without real rounding conventions. -/
theorem cubic_lower_bound (N m : ℕ) (hm : 2 * m ^ 3 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ A.card = m ∧ PowerSumFree A := by
  apply exists_power_free_in_interval N m
  by_cases h : m = 0
  · simp_all
  have h1 : 1 ≤ m := by omega
  have hsq : m ^ 2 ≤ m ^ 3 := by nlinarith [sq_nonneg (m : ℤ)]
  nlinarith

/-- A concrete twelve-element instance in [1,1000], still checked without enumerating subsets. -/
theorem example_twelve :
    (multiples 79 12).card = 12 ∧ multiples 79 12 ⊆ Icc 1 1000 ∧
      PowerSumFree (multiples 79 12) := by
  refine ⟨multiples_card (by decide) 12, ?_, multiples_power_free (by norm_num) ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    have := mem_range.mp hi
    rw [mem_Icc]
    omega
  · have := triangle_double 12
    omega

/-- A squarefree multiplier has the same perfect-power obstruction as a prime. -/
theorem squarefree_mul_not_power {a t : ℕ} (ha : Squarefree a)
    (ht : 0 < t) (hlt : t < a) (x k : ℕ) (hk : 2 ≤ k) : a * t ≠ x ^ k := by
  intro he
  have hax : a ∣ x := (ha.dvd_pow_iff_dvd (by omega : k ≠ 0)).mp
    (he ▸ Nat.dvd_mul_right a t)
  have hsq : a ^ 2 ∣ x ^ k :=
    dvd_trans (pow_dvd_pow_of_dvd hax 2) (pow_dvd_pow x hk)
  rw [← he, pow_two] at hsq
  have hat : a ∣ t := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero ha.ne_zero) hsq
  exact (not_le_of_gt hlt) (Nat.le_of_dvd ht hat)

/-- Every feasible positive coefficient sum is realized by a nonempty subset. -/
theorem multiple_sum_realization {d m t : ℕ} (hd : 0 < d)
    (ht : 0 < t) (htm : t ≤ triangle m) :
    ∃ S ⊆ multiples d m, S.Nonempty ∧ ∑ a ∈ S, a = d * t := by
  obtain ⟨T, hT, he⟩ := all_sums_attained m t htm
  have hinj : Function.Injective (fun i : ℕ => d * (i + 1)) := by
    intro i j hij
    have := Nat.mul_left_cancel hd hij
    omega
  refine ⟨T.image (fun i => d * (i + 1)), image_subset_image hT, ?_, ?_⟩
  · apply image_nonempty.mpr
    by_contra hn
    have : T = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [this] at he
    omega
  · rw [sum_image (fun i _ j _ hij => hinj hij), ← mul_sum, he]

theorem squarefree_multiples_power_free {a m : ℕ} (ha : Squarefree a)
    (hm : triangle m < a) : PowerSumFree (multiples a m) := by
  intro S hS hn x k hk
  obtain ⟨T, hT, rfl⟩ := subset_image_iff.mp hS
  have hinj : Function.Injective (fun i : ℕ => a * (i + 1)) := by
    intro i j he
    have := Nat.mul_left_cancel (Nat.pos_of_ne_zero ha.ne_zero) he
    omega
  rw [sum_image (fun i _ j _ he => hinj he), ← mul_sum]
  have hTn : T.Nonempty := image_nonempty.mp hn
  have ht : 0 < ∑ i ∈ T, (i + 1) := sum_pos (by intros; omega) hTn
  exact squarefree_mul_not_power ha ht ((subset_sum_le_triangle hT).trans_lt hm) x k hk

/-- For a squarefree step, square avoidance and all-perfect-power avoidance agree. -/
theorem squarefree_exact_criterion {a : ℕ} (ha : Squarefree a) (m : ℕ) :
    (SquareSumFree (multiples a m) ↔ m * (m + 1) < 2 * a) ∧
    (PowerSumFree (multiples a m) ↔ m * (m + 1) < 2 * a) := by
  have htriangle := triangle_double m
  have hs : SquareSumFree (multiples a m) ↔ triangle m < a := by
    constructor
    · intro h
      by_contra hn
      obtain ⟨S, hS, hne, he⟩ := multiple_sum_realization
        (Nat.pos_of_ne_zero ha.ne_zero) (Nat.pos_of_ne_zero ha.ne_zero)
        (by omega : a ≤ triangle m)
      exact h S hS hne a (by simpa [pow_two] using he)
    · intro hm
      exact power_free_square_free (squarefree_multiples_power_free ha hm)
  refine ⟨?_, ?_⟩
  · rw [hs]; omega
  · constructor
    · intro h
      have := hs.mp (power_free_square_free h)
      omega
    · intro h
      exact squarefree_multiples_power_free ha (by omega)

/-- A positive square factor may be cancelled from an equality to a square. -/
theorem cancel_square_factor {b t x : ℕ} (hb : 0 < b) (he : b ^ 2 * t = x ^ 2) :
    ∃ y : ℕ, t = y ^ 2 := by
  have hd : b ^ 2 ∣ x ^ 2 := he ▸ Nat.dvd_mul_right (b ^ 2) t
  obtain ⟨y, rfl⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hd
  refine ⟨y, ?_⟩
  rw [mul_pow] at he
  exact Nat.mul_left_cancel (pow_pos hb 2) he

/-- Complete criterion for any positive step given its square-times-squarefree decomposition. -/
theorem general_step_criterion {d a b : ℕ} (ha : Squarefree a) (hb : 0 < b)
    (hd : d = b ^ 2 * a) (m : ℕ) :
    SquareSumFree (multiples d m) ↔ m * (m + 1) < 2 * a := by
  have hap : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hdp : 0 < d := by rw [hd]; positivity
  have htriangle := triangle_double m
  constructor
  · intro h
    by_contra hn
    obtain ⟨S, hS, hne, he⟩ := multiple_sum_realization hdp hap
      (by omega : a ≤ triangle m)
    apply h S hS hne (b * a)
    rw [he, hd]
    ring
  · intro h S hS hn x he
    obtain ⟨T, hT, rfl⟩ := subset_image_iff.mp hS
    have hinj : Function.Injective (fun i : ℕ => d * (i + 1)) := by
      intro i j hij
      have := Nat.mul_left_cancel hdp hij
      omega
    rw [sum_image (fun i _ j _ hij => hinj hij), ← mul_sum, hd, mul_assoc] at he
    obtain ⟨y, hy⟩ := cancel_square_factor hb he
    have hTn : T.Nonempty := image_nonempty.mp hn
    have ht : 0 < ∑ i ∈ T, (i + 1) := sum_pos (by intros; omega) hTn
    have hlt : (∑ i ∈ T, (i + 1)) < a := by
      have := subset_sum_le_triangle hT
      omega
    exact squarefree_mul_not_power ha ht hlt y 2 (by omega) hy

/-- Every positive integer step admits the complete classification. -/
theorem all_positive_steps_classified (d : ℕ) (hd : 0 < d) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree a ∧ d = b ^ 2 * a ∧
      ∀ m : ℕ, SquareSumFree (multiples d m) ↔ m * (m + 1) < 2 * a := by
  obtain ⟨a, b, ha, hb, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos hd
  exact ⟨a, b, ha, hb, hsf, he.symm, general_step_criterion hsf hb he.symm⟩

/-- The general-step result concerns squares: higher powers need not follow. -/
theorem nonsquare_step_does_not_imply_power_avoidance :
    SquareSumFree (multiples 8 1) ∧ ¬ PowerSumFree (multiples 8 1) := by
  constructor
  · apply (general_step_criterion (a := 2) (b := 2)
      (Nat.prime_two.squarefree) (by omega) (by norm_num) 1).mpr
    norm_num
  · intro h
    apply h {8} (by simp [multiples]) (by simp) 2 3 (by omega)
    norm_num

end JSP000476
