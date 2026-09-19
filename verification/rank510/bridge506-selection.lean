import JSP000506Selection

/- Auditor bridge: the intended law is Mathlib's binomial graph law and the
cocolouring predicate is independently stated using pairs of vertices. -/
namespace Verify506
open Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def CoColourable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ (c : Fin n → Fin k) (b : Fin k → Bool),
    ∀ u v, u ≠ v → c u = c v → (G.Adj u v ↔ b (c u) = true)

theorem exists_coColourable {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ k, CoColourable G k := by
  refine ⟨n, id, fun _ => false, ?_⟩
  intro u v hne heq
  exact (hne heq).elim

def coNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.find (exists_coColourable G)

theorem coColourable_iff {n k : ℕ} (G : SimpleGraph (Fin n)) :
    CoColourable G k ↔ JSP000506.CoProper (JSP000506.fromGraph G) k := by
  rw [JSP000506.coProper_iff_all_pairs, JSP000506.toGraph_fromGraph]
  rfl

theorem coNumber_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    coNumber G = Erdos625.cochromaticNumber G := by
  have hz : coNumber G = JSP000506.zeta (JSP000506.fromGraph G) := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ ((coColourable_iff G).mpr
        (JSP000506.zeta_spec (JSP000506.fromGraph G)))
    · exact Nat.find_min' _ ((coColourable_iff G).mp
        (Nat.find_spec (exists_coColourable G)))
  simpa only [JSP000506.zeta_eq_cochromaticNumber, JSP000506.toGraph_fromGraph] using hz

def half : unitInterval := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

theorem intended (M : ℝ) :
    Tendsto (fun n : ℕ =>
      ((SimpleGraph.binomialRandom (Fin n) half)
        {G | M ≤ (G.chromaticNumber.toNat : ℝ) - (coNumber G : ℝ)}).toReal)
      atTop (𝓝 1) := by
  simpa only [JSP000506.gapProbability_eq_standard,
    Erdos625.randomGraphMeasure, Erdos625.chromaticNumberNat,
    coNumber_eq, half, Erdos625.halfProbability] using
    JSP000506.fixed_threshold_tendsto_one M

theorem explicit_quantitative :
    Tendsto (fun n : ℕ =>
      ((SimpleGraph.binomialRandom (Fin n) half)
        {G | ((Real.log 2)^2 / 4 * Real.log (200 / 153 : ℝ)) *
          (n : ℝ) / (Real.log (n : ℝ))^3 ≤
          (G.chromaticNumber.toNat : ℝ) - (coNumber G : ℝ)}).toReal)
      atTop (𝓝 1) := by
  simpa only [JSP000506.gapProbability_eq_standard,
    Erdos625.randomGraphMeasure, Erdos625.chromaticNumberNat,
    Erdos625.gapScale, Erdos625.gapConstant,
    coNumber_eq, half, Erdos625.halfProbability] using
    JSP000506.quantitative_gap_tendsto_one

theorem explicit_scale_diverges :
    Tendsto (fun n : ℕ => ((Real.log 2)^2 / 4 * Real.log (200 / 153 : ℝ)) *
      (n : ℝ) / (Real.log (n : ℝ))^3) atTop atTop := by
  simpa only [Erdos625.gapScale, Erdos625.gapConstant] using
    JSP000506.gapScale_tendsto_atTop

/- Explicit finite counting normalisation and conditional-event formula.
No independence of a graph and its complement is assumed. -/
theorem conditional_explicit
    (B : (n : ℕ) → Finset (Finset (JSP000506.Edge n))) (f : ℕ → ℝ)
    (hB : ∀ᶠ n : ℕ in atTop, 0 < (JSP000506.mass (B n) : ℝ))
    (hratio : Tendsto (fun n => (1 - JSP000506.gapProbability n (f n)) /
      (JSP000506.mass (B n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (JSP000506.mass ((JSP000506.event fun s : Finset (JSP000506.Edge n) =>
        f n ≤ ((JSP000506.chi s - JSP000506.zeta s : ℕ) : ℝ) ∧
        f n ≤ ((JSP000506.chi sᶜ - JSP000506.zeta sᶜ : ℕ) : ℝ)) ∩ B n) : ℝ) /
      (JSP000506.mass (B n) : ℝ)) atTop (𝓝 1) := by
  exact JSP000506.conditional_joint_gap_tendsto_one B f hB hratio

theorem expectation_explicit :
    Tendsto (fun n : ℕ =>
      (∑ s : Finset (JSP000506.Edge n),
        ((min (JSP000506.chi s - JSP000506.zeta s)
          (JSP000506.chi sᶜ - JSP000506.zeta sᶜ) : ℕ) : ℝ)) /
      (2 : ℝ) ^ Fintype.card (JSP000506.Edge n)) atTop atTop := by
  exact JSP000506.mean_minimum_pair_gap_tendsto_atTop

end
end Verify506
