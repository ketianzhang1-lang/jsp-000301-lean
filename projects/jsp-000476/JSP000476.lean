/-
Copyright 2026. Released under the Apache License, Version 2.0.

JSP-000476 / Erdos 587: exact threshold for the classical squarefree-
multiple construction. This is a partial result, not the full extremal
asymptotic theorem. Written with OpenAI ChatGPT assistance after reading
the prior prime-multiple construction in plby/lean-proofs; see README.md.
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace JSP000476
open Finset

/-- The sum of the integers from 1 through k. -/
def triangular (k : ℕ) : ℕ := ∑ i ∈ Icc 1 k, i

@[simp] theorem triangular_zero : triangular 0 = 0 := by simp [triangular]

theorem triangular_succ (k : ℕ) :
    triangular (k + 1) = triangular k + (k + 1) := by
  exact sum_Icc_succ_top (by omega) (fun i : ℕ => i)

theorem le_triangular (k : ℕ) : k ≤ triangular k := by
  induction k with
  | zero => simp
  | succ k ih => rw [triangular_succ]; omega

theorem triangular_mul_two (k : ℕ) : triangular k * 2 = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [triangular_succ]; nlinarith

theorem triangular_eq (k : ℕ) : triangular k = k * (k + 1) / 2 := by
  rw [← triangular_mul_two, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Every integer between zero and the triangular sum is a subset sum. -/
theorem exists_subset_sum_Icc (k t : ℕ) (ht : t ≤ triangular k) :
    ∃ S ⊆ Icc 1 k, ∑ i ∈ S, i = t := by
  induction k generalizing t with
  | zero =>
      have : t = 0 := by simpa using ht
      subst t
      exact ⟨∅, empty_subset _, by simp⟩
  | succ k ih =>
      by_cases hsmall : t ≤ triangular k
      · obtain ⟨S, hS, hsum⟩ := ih t hsmall
        refine ⟨S, ?_, hsum⟩
        intro i hi
        have := mem_Icc.mp (hS hi)
        exact mem_Icc.mpr ⟨this.1, by omega⟩
      · have hk := le_triangular k
        have htk : k + 1 ≤ t := by omega
        have hrem : t - (k + 1) ≤ triangular k := by
          rw [triangular_succ] at ht
          omega
        obtain ⟨S, hS, hsum⟩ := ih (t - (k + 1)) hrem
        have hnot : k + 1 ∉ S := by
          intro h
          have := (mem_Icc.mp (hS h)).2
          omega
        refine ⟨insert (k + 1) S, ?_, ?_⟩
        · intro i hi
          rcases mem_insert.mp hi with rfl | hi
          · exact mem_Icc.mpr ⟨by omega, le_rfl⟩
          · have := mem_Icc.mp (hS hi)
            exact mem_Icc.mpr ⟨this.1, by omega⟩
        · rw [sum_insert hnot, hsum]
          omega

/-- The finite set {q, 2q, ..., kq}. -/
def multiples (q k : ℕ) : Finset ℕ := (Icc 1 k).image (q * ·)

/-- No nonempty subset has a square as its sum. -/
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ¬ IsSquare (∑ a ∈ S, a)

theorem card_multiples (q k : ℕ) (hq : 0 < q) : (multiples q k).card = k := by
  rw [multiples, card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  simp

theorem sum_multiples (q k : ℕ) (hq : 0 < q) :
    ∑ a ∈ multiples q k, a = q * triangular k := by
  rw [multiples, sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  exact (mul_sum _ _ _).symm

/-- Sufficiency: all nonempty sums are positive multiples of q below q². -/
theorem squareSumFree_multiples_of_lt {q k : ℕ} (hq : Squarefree q)
    (hk : triangular k < q) : SquareSumFree (multiples q k) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  intro S hS hne hsquare
  have hdiv : q ∣ ∑ a ∈ S, a := by
    apply dvd_sum
    intro a ha
    obtain ⟨i, _, rfl⟩ := mem_image.mp (hS ha)
    exact dvd_mul_right _ _
  have hpos : 0 < ∑ a ∈ S, a := by
    apply sum_pos
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (hS ha)
      exact Nat.mul_pos hqpos (mem_Icc.mp hi).1
    · exact hne
  have hbound : ∑ a ∈ S, a < q * q := by
    calc
      ∑ a ∈ S, a ≤ ∑ a ∈ multiples q k, a := sum_le_sum_of_subset hS
      _ = q * triangular k := sum_multiples q k hqpos
      _ < q * q := Nat.mul_lt_mul_of_pos_left hk hqpos
  obtain ⟨z, hz⟩ := hsquare
  have hzpos : 0 < z := by nlinarith
  have hqz : q ∣ z := (hq.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
    (by simpa only [pow_two, ← hz] using hdiv)
  have := Nat.le_of_dvd hzpos hqz
  nlinarith

/-- Necessity, with a witness: at or above the threshold some subset sums to q². -/
theorem exists_square_subset_multiples {q k : ℕ} (hq : 0 < q)
    (hk : q ≤ triangular k) :
    ∃ S ⊆ multiples q k, S.Nonempty ∧ ∑ a ∈ S, a = q * q := by
  obtain ⟨T, hT, hsum⟩ := exists_subset_sum_Icc k q hk
  have hne : T.Nonempty := by
    by_contra h
    have hempty := not_nonempty_iff_eq_empty.mp h
    simp [hempty] at hsum
    omega
  refine ⟨T.image (q * ·), image_subset_image hT, hne.image _, ?_⟩
  rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h), ← mul_sum, hsum]

/-- Exact criterion, including the empty-set case and the equality boundary. -/
theorem squareSumFree_multiples_iff {q k : ℕ} (hq : Squarefree q) :
    SquareSumFree (multiples q k) ↔ triangular k < q := by
  refine ⟨?_, squareSumFree_multiples_of_lt hq⟩
  intro h
  by_contra hnot
  obtain ⟨S, hS, hne, hsum⟩ :=
    exists_square_subset_multiples (k := k) (Nat.pos_of_ne_zero hq.ne_zero) (by omega)
  exact h S hS hne ⟨q, hsum⟩

theorem prime_multiples_iff {p k : ℕ} (hp : Nat.Prime p) :
    SquareSumFree (multiples p k) ↔ k * (k + 1) / 2 < p := by
  simpa only [triangular_eq] using squareSumFree_multiples_iff (k := k) hp.squarefree

theorem isSquare_square_mul_iff {c t : ℕ} (hc : 0 < c) :
    IsSquare (c ^ 2 * t) ↔ IsSquare t := by
  constructor
  · rintro ⟨z, hz⟩
    have hdiv : c ^ 2 ∣ z ^ 2 := ⟨t, by simpa [pow_two] using hz.symm⟩
    obtain ⟨w, rfl⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hdiv
    refine ⟨w, Nat.eq_of_mul_eq_mul_left (pow_pos hc 2) ?_⟩
    nlinarith [hz]
  · rintro ⟨w, rfl⟩
    exact ⟨c * w, by ring⟩

/-- Multiplication of every element by a positive square preserves the property. -/
theorem squareSumFree_square_image_iff (A : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    SquareSumFree (A.image (c ^ 2 * ·)) ↔ SquareSumFree A := by
  have hcp : 0 < c ^ 2 := pow_pos hc 2
  have hsum (S : Finset ℕ) :
      (∑ a ∈ S.image (c ^ 2 * ·), a) = c ^ 2 * ∑ a ∈ S, a := by
    rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hcp h), mul_sum]
  constructor
  · intro h S hS hne hsquare
    apply h (S.image (c ^ 2 * ·)) (image_subset_image hS) (hne.image _)
    rw [hsum, isSquare_square_mul_iff hc]
    exact hsquare
  · intro h S hS hne hsquare
    obtain ⟨T, hT, rfl⟩ := subset_image_iff.mp hS
    apply h T hT (image_nonempty.mp hne)
    rw [hsum, isSquare_square_mul_iff hc] at hsquare
    exact hsquare

/-- Full classification for this construction when m = c²q is given in squarefree form. -/
theorem square_part_multiples_iff {c q k : ℕ} (hc : 0 < c) (hq : Squarefree q) :
    SquareSumFree (multiples (c ^ 2 * q) k) ↔ k * (k + 1) / 2 < q := by
  have himage : multiples (c ^ 2 * q) k = (multiples q k).image (c ^ 2 * ·) := by
    simp [multiples, image_image, Function.comp_def, mul_assoc]
  rw [himage, squareSumFree_square_image_iff _ hc, squareSumFree_multiples_iff hq,
    triangular_eq]

/-- Every positive multiplier has such a classification; no primality hypothesis is needed. -/
theorem exists_classification (m : ℕ) (hm : 0 < m) :
    ∃ c q : ℕ, 0 < c ∧ Squarefree q ∧ c ^ 2 * q = m ∧
      ∀ k : ℕ, SquareSumFree (multiples m k) ↔ k * (k + 1) / 2 < q := by
  obtain ⟨c, q, hfactor, hq⟩ := exists_sq_mul_squarefree m
  have hc : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    simp [this] at hfactor
    omega
  exact ⟨c, q, hc, hq, hfactor, fun k => hfactor ▸ square_part_multiples_iff hc hq⟩

/-- Bertrand's postulate and the exact threshold give a uniform integer bound. -/
theorem exists_card_squareSumFree (k N : ℕ) (hN : k ^ 2 * (k + 1) ≤ N) :
    ∃ A ⊆ Icc 1 N, A.card = k ∧ SquareSumFree A := by
  by_cases hk : k = 0
  · subst k
    refine ⟨∅, empty_subset _, by simp, ?_⟩
    intro S hS hne
    have : S = ∅ := subset_empty.mp hS
    simp [this] at hne
  · have hT : triangular k ≠ 0 := by have := le_triangular k; omega
    obtain ⟨p, hp, hpT, hpmax⟩ := Nat.exists_prime_lt_and_le_two_mul (triangular k) hT
    refine ⟨multiples p k, ?_, card_multiples p k hp.pos,
      squareSumFree_multiples_of_lt hp.squarefree hpT⟩
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    refine mem_Icc.mpr ⟨Nat.mul_pos hp.pos (mem_Icc.mp hi).1, ?_⟩
    calc
      p * i ≤ p * k := Nat.mul_le_mul_left p (mem_Icc.mp hi).2
      _ ≤ (2 * triangular k) * k := Nat.mul_le_mul_right k hpmax
      _ = k ^ 2 * (k + 1) := by nlinarith [triangular_mul_two k]
      _ ≤ N := hN

end JSP000476
