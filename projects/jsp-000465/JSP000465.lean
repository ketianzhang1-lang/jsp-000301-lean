/-
Copyright 2026 Ketian Zhang. Licensed under Apache-2.0.
Prepared with OpenAI ChatGPT/Codex assistance.

The counterexample and its substantive bounds are the existing OpenAI proof
in the attributed Erdos180 modules. This module supplies the JSP-000465
interface and simultaneous separation consequences, not a new counterexample.
-/
import ErdosProblems.Erdos180.Quantitative

open Filter
open scoped Topology Classical

namespace JSP000465

open Erdos180

/-- The family convention specializes exactly to Mathlib's ordinary,
non-induced subgraph extremal number. -/
theorem familyExtremal_singleton (H : FiniteGraph) (n : ℕ) :
    familyExtremal {H} n = SimpleGraph.extremalNumber n H.graph := by
  classical
  unfold familyExtremal SimpleGraph.extremalNumber
  congr 1
  ext G
  simp [FamilyFree]

/-- The extremum is attained by a genuine family-free graph at every order.
It is not an empty-set supremum assigned a default value. -/
theorem familyExtremal_attained (n : ℕ) :
    ∃ G : SimpleGraph (Fin n), FamilyFree proposedFamily G ∧
      G.edgeFinset.card = familyExtremal proposedFamily n := by
  classical
  have hbot : FamilyFree proposedFamily (⊥ : SimpleGraph (Fin n)) := by
    intro H hH
    apply SimpleGraph.free_bot
    intro heq
    exact proposedFamily_isCyclic H hH (heq ▸ SimpleGraph.isAcyclic_bot)
  let s := Finset.univ.filter (FamilyFree proposedFamily : SimpleGraph (Fin n) → Prop)
  have hs : s.Nonempty := ⟨⊥, by simpa [s] using hbot⟩
  obtain ⟨G, hG, hmax⟩ := Finset.exists_mem_eq_sup s hs
    (fun G : SimpleGraph (Fin n) => G.edgeFinset.card)
  exact ⟨G, (Finset.mem_filter.mp hG).2, hmax.symm⟩

/-- All forbidden members satisfy one common eventual lower bound. -/
theorem simultaneous_member_lower :
    ∀ᶠ n : ℕ in atTop, ∀ H ∈ proposedFamily,
      manuscriptLowerConstant * (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n H.graph : ℝ) := by
  exact (Filter.eventually_all_finset proposedFamily).mpr
    proposedFamily_uniformMemberLower

/-- Every constant factor is eventually beaten, simultaneously for all
members of the fixed finite family. This is stronger than failure of one
eventual comparison for each member. -/
theorem uniform_separation (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ H ∈ proposedFamily,
      K * (familyExtremal proposedFamily n : ℝ) <
        (SimpleGraph.extremalNumber n H.graph : ℝ) := by
  have hε : 0 < manuscriptLowerConstant / (2 * K) :=
    div_pos manuscriptLowerConstant_pos (mul_pos (by norm_num) hK)
  filter_upwards [proposedFamily_familyLittleO _ hε,
    simultaneous_member_lower, eventually_gt_atTop 0] with n hu hl hn
  intro H hH
  have hscale := extremalScale_pos hn
  have hprod := mul_le_mul_of_nonneg_left hu hK.le
  have hid : K * (manuscriptLowerConstant / (2 * K) * extremalScale n) =
      manuscriptLowerConstant * extremalScale n / 2 := by
    field_simp [ne_of_gt hK]
  rw [hid] at hprod
  have hlow := hl H hH
  change manuscriptLowerConstant * extremalScale n ≤ _ at hlow
  have hpositive := mul_pos manuscriptLowerConstant_pos hscale
  linarith

/-- The connected, bipartite, non-forest restriction is retained in full.
Even constant-factor reduction to a member of the family is impossible. -/
theorem connected_bipartite_counterexample :
    ∃ F : Finset FiniteGraph, F.Nonempty ∧
      (∀ H ∈ F, H.graph.Connected ∧ H.graph.IsBipartite ∧ ¬ H.graph.IsAcyclic) ∧
      ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop, ∀ H ∈ F,
        K * (familyExtremal F n : ℝ) <
          (SimpleGraph.extremalNumber n H.graph : ℝ) := by
  refine ⟨proposedFamily, proposedFamily_nonempty, ?_, uniform_separation⟩
  intro H hH
  exact ⟨proposedFamily_member_connected hH, proposedFamily_member_isBipartite hH,
    proposedFamily_isCyclic H hH⟩

/-- Negative answer to the compactness question with at least one bipartite
member. All quantifiers range over finite simple graphs and all sufficiently
large natural host orders; no unproved conjecture is imported. -/
theorem not_bipartite_compactness :
    ¬ (∀ F : Finset FiniteGraph, F.Nonempty →
      (∃ H ∈ F, H.graph.IsBipartite) →
      ∃ H ∈ F, ∃ K : ℝ, 0 < K ∧
        ∀ᶠ n : ℕ in atTop,
          (SimpleGraph.extremalNumber n H.graph : ℝ) ≤
            K * (familyExtremal F n : ℝ)) := by
  intro h
  obtain ⟨H₀, hH₀⟩ := proposedFamily_nonempty
  obtain ⟨H, hH, K, hK, hbound⟩ :=
    h proposedFamily proposedFamily_nonempty
      ⟨H₀, hH₀, proposedFamily_member_isBipartite hH₀⟩
  obtain ⟨n, hsep, hle⟩ := ((uniform_separation K hK).and hbound).exists
  exact (not_lt_of_ge hle) (hsep H hH)

end JSP000465
