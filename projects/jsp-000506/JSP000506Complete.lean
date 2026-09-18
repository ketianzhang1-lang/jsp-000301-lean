/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import JSP000506Bridge

/-!
The complete original random-graph conclusion, in our original exact
counting model, together with the retained finite concentration theorem.
Samuil Petkov's quantitative theorem is an attributed dependency. We prove
the graph-model, probability, threshold and full-sequence bridges here.
-/

namespace JSP000506
open Filter Finset
open scoped Topology

noncomputable section

/-- Our exact probability that the natural chromatic/cochromatic gap is at
least a real threshold. Natural subtraction is justified by `zeta_le_chi`. -/
def gapProbability (n : ℕ) (threshold : ℝ) : ℝ :=
  (mass (event fun s : Finset (Edge n) => threshold ≤ ((chi s - zeta s : ℕ) : ℝ)) : ℝ)

theorem gapProbability_nonneg (n : ℕ) (threshold : ℝ) :
    0 ≤ gapProbability n threshold := by
  exact_mod_cast mass_nonneg _

theorem gapProbability_le_one (n : ℕ) (threshold : ℝ) :
    gapProbability n threshold ≤ 1 := by
  exact_mod_cast mass_le_one _

theorem gapProbability_antitone (n : ℕ) : Antitone (gapProbability n) := by
  intro a b hab
  apply Rat.cast_le.mpr
  apply mass_mono
  intro s hs
  simp only [mem_event] at hs ⊢
  exact hab.trans hs

theorem gapProbability_eq_standard (n : ℕ) (threshold : ℝ) :
    gapProbability n threshold =
      (Erdos625.randomGraphMeasure n {G |
        threshold ≤ (Erdos625.chromaticNumberNat G : ℝ) -
          (Erdos625.cochromaticNumber G : ℝ)}).toReal := by
  unfold gapProbability
  simp only [gap_cast_eq]
  exact mass_event_eq_randomGraph n _

/-- The full quantitative theorem transferred to our exact counting model. -/
theorem quantitative_gap_tendsto_one :
    Tendsto (fun n => gapProbability n (Erdos625.gapScale n)) atTop (𝓝 1) := by
  have h := Erdos625.erdos625Statement_iff_real.mp Erdos625.erdos625
  simpa only [gapProbability_eq_standard, Erdos625.gapProbability,
    Erdos625.gapEvent] using h

/-- The positive quantitative scale diverges along all natural orders. -/
theorem gapScale_tendsto_atTop : Tendsto Erdos625.gapScale atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_exp_div_pow_atTop 3).comp hlog
  have h' : Tendsto (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ) ^ 3) atTop atTop := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Function.comp_apply, Real.exp_log (by exact_mod_cast hn)]
  have hc := h'.const_mul_atTop Erdos625.gapConstant_pos
  simpa only [Erdos625.gapScale, mul_div_assoc] using hc

/-- Any deterministic threshold eventually below the proven scale is met
with probability tending to one. This includes nonmonotone thresholds. -/
theorem threshold_tendsto_one (f : ℕ → ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ Erdos625.gapScale n) :
    Tendsto (fun n => gapProbability n (f n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    quantitative_gap_tendsto_one tendsto_const_nhds
  · exact hf.mono fun n hn => gapProbability_antitone n hn
  · exact Eventually.of_forall fun n => gapProbability_le_one n _

/-- Original Erdős--Gimbel conclusion: every fixed real gap threshold is
exceeded with probability tending to one along the full sequence. -/
theorem fixed_threshold_tendsto_one (M : ℝ) :
    Tendsto (fun n => gapProbability n M) atTop (𝓝 1) :=
  threshold_tendsto_one (fun _ => M) (gapScale_tendsto_atTop.eventually_ge_atTop M)

theorem small_gap_probability_tendsto_zero (g : ℕ) :
    Tendsto (fun n => (mass (event fun s : Finset (Edge n) =>
      chi s - zeta s ≤ g) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_const_nhds.sub (fixed_threshold_tendsto_one (g + 1 : ℝ))
  have heq (n : ℕ) :
      (mass (event fun s : Finset (Edge n) => chi s - zeta s ≤ g) : ℝ) =
        1 - gapProbability n (g + 1 : ℝ) := by
    have hevent : (event fun s : Finset (Edge n) => chi s - zeta s ≤ g) =
        (event fun s : Finset (Edge n) =>
          (g + 1 : ℝ) ≤ ((chi s - zeta s : ℕ) : ℝ))ᶜ := by
      ext s
      simp only [mem_event, mem_compl]
      push_cast
      norm_cast
      omega
    rw [hevent, mass_compl]
    push_cast
    rfl
  simpa only [sub_self] using h.congr (fun n => (heq n).symm)

/-- The old high-probability small-gap premise eventually fails for every
fixed width. It is not assumed in the complete original theorem. -/
theorem eventually_not_heckel_premise (g : ℕ) :
    ∀ᶠ n : ℕ in atTop, ¬ ((999 : ℚ) / 1000 ≤
      mass (event fun s : Finset (Edge n) => chi s - zeta s ≤ g)) := by
  have h := (small_gap_probability_tendsto_zero g).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 999 / 1000))
  filter_upwards [h] with n hn
  intro hbad
  have hb : (999 : ℝ) / 1000 ≤
      (mass (event fun s : Finset (Edge n) => chi s - zeta s ≤ g) : ℝ) := by
    exact_mod_cast hbad
  linarith

/-- Complete original statement with literal rational counting probabilities. -/
theorem jsp_000506 :
    ∀ g : ℕ, Tendsto (fun n => (mass (event fun s : Finset (Edge n) =>
      g ≤ chi s - zeta s) : ℝ)) atTop (𝓝 1) := by
  intro g
  simpa only [gapProbability, Nat.cast_le] using fixed_threshold_tendsto_one (g : ℝ)

/-- Both the full asymptotic resolution and our retained finite theorem,
with all orders and all widths quantified explicitly. -/
theorem complete_package :
    (∀ g : ℕ, Tendsto (fun n => (mass (event fun s : Finset (Edge n) =>
      g ≤ chi s - zeta s) : ℝ)) atTop (𝓝 1)) ∧
    (∀ n g : ℕ, (999 : ℚ) / 1000 ≤
      mass (event fun s : Finset (Edge n) => chi s - zeta s ≤ g) →
      ∃ k : ℕ, (9 : ℚ) / 10 <
        mass (event fun s : Finset (Edge n) => k ≤ chi s ∧ chi s ≤ k + g)) :=
  ⟨jsp_000506, heckel_proposition3⟩

end
end JSP000506
