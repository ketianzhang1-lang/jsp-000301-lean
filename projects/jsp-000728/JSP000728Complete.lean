import JSP000728Bridge
import ErdosProblems.Erdos877

/-!
# Original maximal sum-free counting question

We retain our independent all-N Cameron–Erdős lower-bound construction and prove
the exact finite-family bridge in JSP000728Bridge. We use the attributed, pinned
upper-bound proof from plby/lean-proofs to answer the original relative-count
question, including a fixed exponential saving over the number of all sum-free
sets. We do not claim the later sharp exponent 1/4 or residue-class constants.
-/

open Filter
open scoped Topology

namespace JSP000728

theorem maximalCount_isLittleO_benchmark :
    (fun N : ℕ => ((maximalSets N).card : ℝ)) =o[atTop]
      (fun N : ℕ => Real.rpow 2 ((N : ℝ) / 2)) := by
  simpa only [maximalSets_card_eq_upstream] using Erdos877.erdos_877

theorem maximalCount_exponential_bound :
    ∀ᶠ N : ℕ in atTop, ((maximalSets N).card : ℝ) ≤
      Real.rpow 2 (Erdos877.resolutionExponent * (N : ℝ)) := by
  simpa only [maximalSets_card_eq_upstream] using Erdos877.erdos_877_exponential_bound

/-- Our lower-bound construction also applies to the imported count exactly. -/
theorem upstream_count_lower_bound (N : ℕ) :
    2 ^ (N / 4) ≤ Erdos877.maximalSumFreeCount N := by
  rw [← maximalSets_card_eq_upstream]
  exact cameron_erdos_lower_bound N

/-- The original question: maximal sets have vanishing density among all sets. -/
theorem maximalCount_isLittleO_allCount :
    (fun N : ℕ => ((maximalSets N).card : ℝ)) =o[atTop]
      (fun N : ℕ => ((allSumFreeSets N).card : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [maximalCount_isLittleO_benchmark.bound hc] with N hN
  have hbench := benchmark_le_allSumFreeSets N
  have hb0 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((N : ℝ) / 2)
  simp only [Real.norm_eq_abs, Real.rpow_eq_pow, Nat.abs_cast,
    abs_of_nonneg hb0] at hN ⊢
  exact hN.trans (mul_le_mul_of_nonneg_left hbench hc.le)

theorem maximal_to_all_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => ((maximalSets N).card : ℝ) /
      ((allSumFreeSets N).card : ℝ)) atTop (𝓝 0) :=
  maximalCount_isLittleO_allCount.tendsto_div_nhds_zero

/-- The stronger form explicitly asked by Cameron and Erdős. -/
theorem relative_exponential_saving :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ((maximalSets N).card : ℝ) ≤
        ((allSumFreeSets N).card : ℝ) / Real.rpow 2 (δ * (N : ℝ)) := by
  refine ⟨1 / 2 - Erdos877.resolutionExponent,
    sub_pos.mpr Erdos877.resolutionExponent_lt_half, ?_⟩
  filter_upwards [maximalCount_exponential_bound] with N hN
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)).mpr
  calc
    ((maximalSets N).card : ℝ) *
        Real.rpow 2 ((1 / 2 - Erdos877.resolutionExponent) * (N : ℝ)) ≤
        Real.rpow 2 (Erdos877.resolutionExponent * (N : ℝ)) *
        Real.rpow 2 ((1 / 2 - Erdos877.resolutionExponent) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (by norm_num) _)
    _ = Real.rpow 2 ((N : ℝ) / 2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ ((allSumFreeSets N).card : ℝ) := benchmark_le_allSumFreeSets N

/-- Complete original relative-count question, together with our all-N lower bound. -/
theorem jsp_000728 :
    (∀ N : ℕ, 2 ^ (N / 4) ≤ (maximalSets N).card) ∧
    ((fun N : ℕ => ((maximalSets N).card : ℝ)) =o[atTop]
      (fun N : ℕ => ((allSumFreeSets N).card : ℝ))) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ((maximalSets N).card : ℝ) ≤
        ((allSumFreeSets N).card : ℝ) / Real.rpow 2 (δ * (N : ℝ))) :=
  ⟨cameron_erdos_lower_bound, maximalCount_isLittleO_allCount,
    relative_exponential_saving⟩

end JSP000728
