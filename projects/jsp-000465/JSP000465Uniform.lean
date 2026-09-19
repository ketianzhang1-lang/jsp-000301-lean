/-
Copyright (c) 2026 ketianzhang1-lang. Released under Apache 2.0.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance.

Uniform ratio and adaptive-selector consequences of the existing compactness
counterexample. The substantive construction and estimates remain credited to
OpenAI/Astra in the imported Erdos180 development. No new mathematical
counterexample or global first-formalization claim is made.
-/
import JSP000465

open Filter
open scoped Topology Classical

namespace JSP000465
open Erdos180

/-- All member extrema are eventually positive, simultaneously. -/
theorem eventually_member_positive :
    ∀ᶠ n : ℕ in atTop, ∀ H ∈ proposedFamily,
      0 < (SimpleGraph.extremalNumber n H.graph : ℝ) := by
  filter_upwards [simultaneous_member_lower, eventually_gt_atTop 0] with n hl hn
  intro H hH
  have hp := mul_pos manuscriptLowerConstant_pos (extremalScale_pos hn)
  have hb := hl H hH
  change manuscriptLowerConstant * extremalScale n ≤ _ at hb
  exact hp.trans_le hb

/-- One threshold controls the relative gap for every member of the fixed family. -/
theorem uniform_ratio_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H ∈ proposedFamily,
      0 < (SimpleGraph.extremalNumber n H.graph : ℝ) ∧
      (familyExtremal proposedFamily n : ℝ) /
        (SimpleGraph.extremalNumber n H.graph : ℝ) < ε := by
  filter_upwards [eventually_member_positive, uniform_separation ε⁻¹ (inv_pos.mpr hε)]
    with n hp hs
  intro H hH
  refine ⟨hp H hH, (div_lt_iff₀ (hp H hH)).mpr ?_⟩
  calc
    (familyExtremal proposedFamily n : ℝ) =
        ε * (ε⁻¹ * (familyExtremal proposedFamily n : ℝ)) := by
          field_simp [ne_of_gt hε]
    _ < ε * (SimpleGraph.extremalNumber n H.graph : ℝ) :=
      mul_lt_mul_of_pos_left (hs H hH) hε

/-- The comparison member may depend arbitrarily on n, and membership is needed
only eventually. No monotonicity or fixed member is assumed. -/
theorem adaptive_ratio_tendsto (σ : ℕ → FiniteGraph)
    (hσ : ∀ᶠ n : ℕ in atTop, σ n ∈ proposedFamily) :
    Tendsto (fun n : ℕ => (familyExtremal proposedFamily n : ℝ) /
      (SimpleGraph.extremalNumber n (σ n).graph : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hσ.and (uniform_ratio_small ε hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  exact ((hN n hn).2 (σ n) (hN n hn).1).2

/-- Even an n-dependent choice cannot supply an eventual constant-factor bound. -/
theorem no_adaptive_comparison (σ : ℕ → FiniteGraph)
    (hσ : ∀ᶠ n : ℕ in atTop, σ n ∈ proposedFamily)
    (K : ℝ) (hK : 0 < K) :
    ¬ (∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n (σ n).graph : ℝ) ≤
        K * (familyExtremal proposedFamily n : ℝ)) := by
  intro hbound
  obtain ⟨n, hn⟩ := (hσ.and ((uniform_separation K hK).and hbound)).exists
  exact (not_lt_of_ge hn.2.2) (hn.2.1 (σ n) hn.1)

/-- Explicit negation of the adaptive version, with every family member connected,
bipartite and cyclic as in the original counterexample. -/
theorem adaptive_compactness_counterexample :
    ∃ F : Finset FiniteGraph, F.Nonempty ∧
      (∀ H ∈ F, H.graph.Connected ∧ H.graph.IsBipartite ∧ ¬ H.graph.IsAcyclic) ∧
      ¬ ∃ (σ : ℕ → FiniteGraph) (K : ℝ),
        (∀ᶠ n : ℕ in atTop, σ n ∈ F) ∧ 0 < K ∧
        (∀ᶠ n : ℕ in atTop,
          (SimpleGraph.extremalNumber n (σ n).graph : ℝ) ≤
            K * (familyExtremal F n : ℝ)) := by
  refine ⟨proposedFamily, proposedFamily_nonempty, ?_, ?_⟩
  · intro H hH
    exact ⟨proposedFamily_member_connected hH, proposedFamily_member_isBipartite hH,
      proposedFamily_isCyclic H hH⟩
  · rintro ⟨σ, K, hσ, hK, hbound⟩
    exact no_adaptive_comparison σ hσ K hK hbound

end JSP000465
