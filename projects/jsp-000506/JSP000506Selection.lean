/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import JSP000506Complete

/-!
Exact finite-probability consequences for JSP-000506: simultaneous gaps in
a graph and its complement, and robustness under conditioning on an arbitrary
set of graphs. No independence, monotonicity or graph-invariance assumption
is imposed on the conditioning sets. Rare conditioning is allowed only with
an explicit vanishing failure-probability ratio.

These are our formal extensions of the credited complete development.
Petkov's quantitative theorem and Heckel's finite reduction retain their
original authorship. We do not claim new mathematical discovery or priority.
-/

namespace JSP000506
open Filter Finset
open scoped Topology
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite union bound, in the exact counting model. -/
theorem intersection_probability_lower (A B : Finset (Finset α)) :
    (mass A : ℝ) + (mass B : ℝ) - 1 ≤ (mass (A ∩ B) : ℝ) := by
  classical
  have hcover : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro s hs
    by_cases hb : s ∈ B
    · exact mem_union_left _ (mem_inter.mpr ⟨hs, hb⟩)
    · exact mem_union_right _ (mem_compl.mpr hb)
  have h := mass_cover hcover
  rw [mass_compl] at h
  have hq : mass A + mass B - 1 ≤ mass (A ∩ B) := by linarith
  exact_mod_cast hq

/-- Conditional counting probability. Its use as a conditional distribution
requires positive conditioning mass, stated in the theorems below. -/
def conditionalProbability (A B : Finset (Finset α)) : ℝ :=
  (mass (A ∩ B) : ℝ) / (mass B : ℝ)

/-- Conditioning can magnify failure by at most the inverse retained mass. -/
theorem conditional_failure_bounds (A B : Finset (Finset α))
    (hB : 0 < (mass B : ℝ)) :
    0 ≤ 1 - conditionalProbability A B ∧
    1 - conditionalProbability A B ≤ (1 - (mass A : ℝ)) / (mass B : ℝ) := by
  have hsub : (mass (A ∩ B) : ℝ) ≤ (mass B : ℝ) := by
    exact_mod_cast (mass_mono (inter_subset_right : A ∩ B ⊆ B))
  have hu : conditionalProbability A B ≤ 1 := by
    unfold conditionalProbability
    exact (div_le_one hB).mpr hsub
  refine ⟨by linarith, ?_⟩
  have hl := intersection_probability_lower A B
  unfold conditionalProbability
  rw [one_sub_div hB.ne']
  exact div_le_div_of_nonneg_right (by linarith) hB.le

/-- Both the graph and its complement have their respective required gaps. -/
def jointGapEvent (n : ℕ) (a b : ℝ) : Finset (Finset (Edge n)) :=
  event fun s => a ≤ ((chi s - zeta s : ℕ) : ℝ) ∧
    b ≤ ((chi sᶜ - zeta sᶜ : ℕ) : ℝ)

def jointGapProbability (n : ℕ) (a b : ℝ) : ℝ :=
  (mass (jointGapEvent n a b) : ℝ)

/-- Exact finite-n bound; independence of G and its complement is not used. -/
theorem joint_gap_probability_bounds (n : ℕ) (a b : ℝ) :
    gapProbability n a + gapProbability n b - 1 ≤ jointGapProbability n a b ∧
    jointGapProbability n a b ≤ 1 := by
  classical
  let A := event fun s : Finset (Edge n) => a ≤ ((chi s - zeta s : ℕ) : ℝ)
  let B := event fun s : Finset (Edge n) => b ≤ ((chi sᶜ - zeta sᶜ : ℕ) : ℝ)
  have heq : jointGapEvent n a b = A ∩ B := by
    ext s
    simp [jointGapEvent, A, B]
  have hb : (mass B : ℝ) = gapProbability n b := by
    dsimp [B, gapProbability]
    exact congrArg (fun q : ℚ => (q : ℝ))
      (mass_event_compl (fun s : Finset (Edge n) => b ≤ ((chi s - zeta s : ℕ) : ℝ)))
  constructor
  · have h := intersection_probability_lower A B
    rw [hb, ← heq] at h
    exact h
  · unfold jointGapProbability
    exact_mod_cast (mass_le_one (jointGapEvent n a b))

/-- The quantitative gap scale holds simultaneously for G and its complement. -/
theorem joint_quantitative_gap_tendsto_one :
    Tendsto (fun n => jointGapProbability n (Erdos625.gapScale n)
      (Erdos625.gapScale n)) atTop (𝓝 1) := by
  have hl := (quantitative_gap_tendsto_one.add quantitative_gap_tendsto_one).sub
    (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    exact (joint_gap_probability_bounds n _ _).1
  · intro n
    exact (joint_gap_probability_bounds n _ _).2

/-- Two arbitrary nonmonotone thresholds below the proven scale may be used. -/
theorem joint_threshold_tendsto_one (f g : ℕ → ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ Erdos625.gapScale n)
    (hg : ∀ᶠ n : ℕ in atTop, g n ≤ Erdos625.gapScale n) :
    Tendsto (fun n => jointGapProbability n (f n) (g n)) atTop (𝓝 1) := by
  have hl := ((threshold_tendsto_one f hf).add
    (threshold_tendsto_one g hg)).sub (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    exact (joint_gap_probability_bounds n _ _).1
  · intro n
    exact (joint_gap_probability_bounds n _ _).2

/-- A finite-n bound for the joint failure probability after arbitrary
conditioning. The factor 2 comes from the complement union bound. -/
theorem conditional_joint_failure_bounds (n : ℕ) (t : ℝ)
    (B : Finset (Finset (Edge n))) (hB : 0 < (mass B : ℝ)) :
    0 ≤ 1 - conditionalProbability (jointGapEvent n t t) B ∧
    1 - conditionalProbability (jointGapEvent n t t) B ≤
      (2 * (1 - gapProbability n t)) / (mass B : ℝ) := by
  have h := conditional_failure_bounds (jointGapEvent n t t) B hB
  have hj := (joint_gap_probability_bounds n t t).1
  refine ⟨h.1, h.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ hB.le
  change 1 - jointGapProbability n t t ≤ 2 * (1 - gapProbability n t)
  linarith

/-- Rare, graph-dependent conditioning preserves the joint conclusion if
the unconditioned failure probability is negligible relative to retained mass.
This condition is essential; arbitrary vanishing conditioning mass alone
would not suffice. -/
theorem conditional_joint_gap_tendsto_one
    (B : (n : ℕ) → Finset (Finset (Edge n))) (f : ℕ → ℝ)
    (hB : ∀ᶠ n : ℕ in atTop, 0 < (mass (B n) : ℝ))
    (hratio : Tendsto (fun n => (1 - gapProbability n (f n)) /
      (mass (B n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => conditionalProbability (jointGapEvent n (f n) (f n))
      (B n)) atTop (𝓝 1) := by
  have hu := hratio.const_mul 2
  simp only [mul_zero] at hu
  have hz : Tendsto (fun n => 1 - conditionalProbability
      (jointGapEvent n (f n) (f n)) (B n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact hB.mono fun n hn => (conditional_joint_failure_bounds n (f n) (B n) hn).1
    · filter_upwards [hB] with n hn
      simpa only [mul_div_assoc] using
        (conditional_joint_failure_bounds n (f n) (B n) hn).2
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  simpa only [sub_zero, sub_sub_cancel] using h

/-- In particular, conditioning on any family retaining a fixed positive
fraction of all graphs preserves every threshold below the quantitative scale. -/
theorem positive_mass_conditioning_tendsto_one
    (B : (n : ℕ) → Finset (Finset (Edge n))) (f : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hB : ∀ᶠ n : ℕ in atTop, c ≤ (mass (B n) : ℝ))
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ Erdos625.gapScale n) :
    Tendsto (fun n => conditionalProbability (jointGapEvent n (f n) (f n))
      (B n)) atTop (𝓝 1) := by
  have hp : ∀ᶠ n : ℕ in atTop, 0 < (mass (B n) : ℝ) :=
    hB.mono fun _ h => hc.trans_le h
  apply conditional_joint_gap_tendsto_one B f hp
  have hz := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (threshold_tendsto_one f hf)).div_const c
  simp only [sub_self, zero_div] at hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · filter_upwards [hp] with n hn
    exact div_nonneg (sub_nonneg.mpr (gapProbability_le_one n _)) hn.le
  · filter_upwards [hB] with n hn
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr (gapProbability_le_one n _)) hc hn

/-- The smaller of the two gaps is the robust gap for a graph/complement pair. -/
def minimumPairGap {n : ℕ} (s : Finset (Edge n)) : ℕ :=
  min (chi s - zeta s) (chi sᶜ - zeta sᶜ)

/-- Exact uniform expectation over all simple labelled graphs. -/
def meanMinimumPairGap (n : ℕ) : ℝ :=
  (∑ s : Finset (Edge n), (minimumPairGap s : ℝ)) /
    (2 : ℝ) ^ Fintype.card (Edge n)

/-- A finite-n tail lower bound for the expectation of the smaller gap. -/
theorem mean_minimum_pair_gap_lower (n : ℕ) (t : ℝ) :
    t * jointGapProbability n t t ≤ meanMinimumPairGap n := by
  classical
  let A := jointGapEvent n t t
  have hsum : ∑ s ∈ A, t ≤ ∑ s ∈ A, (minimumPairGap s : ℝ) := by
    apply sum_le_sum
    intro s hs
    have hh : t ≤ ((chi s - zeta s : ℕ) : ℝ) ∧
        t ≤ ((chi sᶜ - zeta sᶜ : ℕ) : ℝ) := by
      simpa only [A, jointGapEvent, mem_event] using hs
    simpa only [minimumPairGap, Nat.cast_min] using le_min hh.1 hh.2
  have hfull : (∑ s ∈ A, (minimumPairGap s : ℝ)) ≤
      ∑ s : Finset (Edge n), (minimumPairGap s : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ A)
    intro s _ _
    positivity
  have hbound : t * (A.card : ℝ) ≤
      ∑ s : Finset (Edge n), (minimumPairGap s : ℝ) := by
    simpa only [sum_const, nsmul_eq_mul, mul_comm] using hsum.trans hfull
  have h := div_le_div_of_nonneg_right hbound
    (by positivity : 0 ≤ (2 : ℝ) ^ Fintype.card (Edge n))
  simpa only [meanMinimumPairGap, jointGapProbability, mass,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat,
    mul_div_assoc, A] using h

/-- Every coefficient strictly below one eventually lower-bounds the expected
smaller gap relative to Petkov's quantitative scale. No upper bound or
asymptotic equality of this expectation is asserted. -/
theorem mean_minimum_pair_gap_scale_lower (c : ℝ) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, c * Erdos625.gapScale n ≤ meanMinimumPairGap n := by
  have hp := joint_quantitative_gap_tendsto_one.eventually (lt_mem_nhds hc)
  have ht := gapScale_tendsto_atTop.eventually_ge_atTop 0
  filter_upwards [hp, ht] with n hn ht
  have hmul := mul_le_mul_of_nonneg_left hn.le ht
  have hle : c * Erdos625.gapScale n ≤ Erdos625.gapScale n *
      jointGapProbability n (Erdos625.gapScale n) (Erdos625.gapScale n) := by
    simpa only [mul_comm] using hmul
  exact hle.trans (mean_minimum_pair_gap_lower n (Erdos625.gapScale n))

/-- Even the expected smaller of the two gaps diverges along all graph orders. -/
theorem mean_minimum_pair_gap_tendsto_atTop :
    Tendsto meanMinimumPairGap atTop atTop := by
  have h := gapScale_tendsto_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  exact tendsto_atTop_mono' atTop
    (mean_minimum_pair_gap_scale_lower (1 / 2) (by norm_num)) h

end
end JSP000506
