/-
Copyright 2026 the submitting account ketianzhang1-lang.
Licensed under the Apache License, Version 2.0.
Elementary dilation supplement to the Bremner k = 4 certificate.
Prepared with OpenAI ChatGPT assistance. No new mathematics is claimed.
-/
import JSP000736

namespace JSP000736

/-- Multiplying each factor by t multiplies its difference by t and product by t². -/
theorem scale_factor_difference (t n d : ℕ) (hd : d ∈ factorDifferenceSet n) :
    t * d ∈ factorDifferenceSet (t ^ 2 * n) := by
  rcases hd with ⟨a, b, hab, hd⟩
  refine ⟨t * a, t * b, ?_, ?_⟩
  · rw [hab]; ring
  · push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg (Int.natCast_nonneg t), ← hd]

def scaledNumbers (t : ℕ) : Finset ℕ := numbers.image (fun n => t ^ 2 * n)
def scaledDifferences (t : ℕ) : Finset ℕ := differences.image (fun d => t * d)

theorem scaled_cardinalities (t : ℕ) (ht : 0 < t) :
    (scaledNumbers t).card = 4 ∧ (scaledDifferences t).card = 4 := by
  constructor
  · rw [scaledNumbers, Finset.card_image_of_injective _
      (fun _ _ h => Nat.mul_left_cancel (pow_pos ht 2) h)]
    decide
  · rw [scaledDifferences, Finset.card_image_of_injective _
      (fun _ _ h => Nat.mul_left_cancel ht h)]
    decide

theorem scaled_common_differences (t : ℕ) :
    (↑(scaledDifferences t) : Set ℕ) ⊆ ⋂ n ∈ scaledNumbers t, factorDifferenceSet n := by
  intro d hd
  obtain ⟨d, hd0, rfl⟩ := Finset.mem_image.mp hd
  simp only [Set.mem_iInter]
  intro n hn
  obtain ⟨n, hn0, rfl⟩ := Finset.mem_image.mp hn
  apply scale_factor_difference
  exact Set.mem_iInter.mp (Set.mem_iInter.mp (common_differences hd0) n) hn0

/-- Every positive dilation satisfies the original k = 4 cardinality condition. -/
theorem scaled_k_eq_4 (t : ℕ) (ht : 0 < t) :
    (∀ n ∈ scaledNumbers t, 1 ≤ n) ∧ (scaledNumbers t).card = 4 ∧
      (⋂ n ∈ scaledNumbers t, factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨?_, (scaled_cardinalities t ht).1, ?_⟩
  · intro n hn
    obtain ⟨n, hn0, rfl⟩ := Finset.mem_image.mp hn
    have hnpos : 0 < n := by
      simp only [numbers, Finset.mem_insert, Finset.mem_singleton] at hn0
      rcases hn0 with rfl | rfl | rfl | rfl <;> norm_num
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos (pow_pos ht 2) hnpos))
  · have hmem : t ^ 2 * 26128575 ∈ scaledNumbers t :=
      Finset.mem_image.mpr ⟨26128575, by decide, rfl⟩
    have hf : (⋂ n ∈ scaledNumbers t, factorDifferenceSet n).Finite :=
      (factorDifferenceSet_finite (t ^ 2 * 26128575) (by positivity)).subset
        (Set.iInter_subset_of_subset (t ^ 2 * 26128575)
          (Set.iInter_subset_of_subset hmem Set.Subset.rfl))
    have hcard := Set.ncard_le_ncard (scaled_common_differences t) hf
    simpa only [Set.ncard_coe_finset, (scaled_cardinalities t ht).2] using hcard

/-- Both all four integers and all four common differences exceed any given bound.
This does not increase the number of common differences beyond four. -/
theorem k_eq_4_above_every_bound (M : ℕ) :
    ∃ Ns Ds : Finset ℕ, Ns.card = 4 ∧ Ds.card = 4 ∧
      (∀ n ∈ Ns, M < n) ∧ (∀ d ∈ Ds, M < d) ∧
      (↑Ds : Set ℕ) ⊆ ⋂ n ∈ Ns, factorDifferenceSet n := by
  refine ⟨scaledNumbers (M + 1), scaledDifferences (M + 1),
    (scaled_cardinalities _ (by omega)).1,
    (scaled_cardinalities _ (by omega)).2, ?_, ?_, scaled_common_differences _⟩
  · intro n hn
    obtain ⟨n, hn0, rfl⟩ := Finset.mem_image.mp hn
    have hnpos : 1 ≤ n := by
      simp only [numbers, Finset.mem_insert, Finset.mem_singleton] at hn0
      rcases hn0 with rfl | rfl | rfl | rfl <;> norm_num
    calc
      M < M + 1 := by omega
      _ ≤ (M + 1) ^ 2 := by nlinarith
      _ ≤ (M + 1) ^ 2 * n := by exact Nat.le_mul_of_pos_right _ hnpos
  · intro d hd
    obtain ⟨d, hd0, rfl⟩ := Finset.mem_image.mp hd
    have hdpos : 1 ≤ d := by
      simp only [differences, Finset.mem_insert, Finset.mem_singleton] at hd0
      rcases hd0 with rfl | rfl | rfl | rfl <;> norm_num
    exact lt_of_lt_of_le (by omega : M < M + 1) (Nat.le_mul_of_pos_right _ hdpos)

/-- Distinct positive scale parameters give distinct four-element sets. -/
theorem scaledNumbers_injective : Function.Injective (fun t : ℕ => scaledNumbers (t + 1)) := by
  have hsum (u : ℕ) (hu : 0 < u) :
      (scaledNumbers u).sum id = u ^ 2 * numbers.sum id := by
    rw [scaledNumbers, Finset.sum_image]
    · simp [Finset.mul_sum]
    · intro a _ b _ hab
      exact Nat.mul_left_cancel (pow_pos hu 2) hab
  intro s t h
  have hs := congrArg (fun S : Finset ℕ => S.sum id) h
  rw [hsum (s + 1) (by omega), hsum (t + 1) (by omega)] at hs
  norm_num [numbers] at hs
  nlinarith

/-- Infinitely many different four-integer witnesses, all for the same k = 4 case. -/
theorem infinitely_many_k_eq_4_witnesses :
    {Ns : Finset ℕ | (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4}.Infinite := by
  apply (Set.infinite_range_of_injective scaledNumbers_injective).mono
  rintro Ns ⟨t, rfl⟩
  exact scaled_k_eq_4 (t + 1) (by omega)

end JSP000736
