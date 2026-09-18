import JSP000585Bridge
import ErdosProblems.Erdos717

/-! We connect our exact finite Catlin certificate to the full uniform
Erdős–Fajtlowicz upper bound. The general upper-bound proof is reused from
the pinned plby/lean-proofs development; UPSTREAM.json records its provenance.
Our additional results identify the two subdivision models, establish the
extremal formulation, and extract a necessary lower bound on its constant. -/

namespace JSP000585
open CatlinComplete CatlinCertificates

theorem subdivisionModels_iff {V : Type*} (G : SimpleGraph V) (r : ℕ) :
    Erdos717.ContainsCliqueSubdivision G r ↔ Erdos718.ContainsCliqueSubdivision G r := by
  constructor
  · rintro ⟨S⟩
    exact ⟨{
      branch := S.branch
      path := S.path
      path_isPath := S.path_isPath
      interior_avoids_branch := S.interior_avoids_branch
      interior_pairwise := S.interior_pairwise
    }⟩
  · exact Erdos717.ContainsCliqueSubdivision.ofErdos718

theorem catlin_subdivision_iff (r : ℕ) :
    Erdos717.ContainsCliqueSubdivision graph r ↔ r ≤ 7 := by
  rw [subdivisionModels_iff, ← containsSubdivision_iff_indexed,
    CatlinComplete.containsCliqueSubdivision_iff]

theorem catlin_sigma_eq_seven : Erdos717.cliqueSubdivisionNumber graph = 7 := by
  apply Nat.le_antisymm
  · exact (catlin_subdivision_iff _).mp
      (Erdos717.containsCliqueSubdivision_cliqueSubdivisionNumber graph)
  · exact Erdos717.le_cliqueSubdivisionNumber ((catlin_subdivision_iff 7).mpr le_rfl)

theorem catlin_chi_eq_eight : Erdos717.chiNat graph = 8 := by
  simp [Erdos717.chiNat, chromaticNumber_eq_eight]

noncomputable def ratio {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (Erdos717.chiNat G : ℝ) / (Erdos717.cliqueSubdivisionNumber G : ℝ)

theorem catlin_ratio_eq : ratio graph = (8 / 7 : ℝ) := by
  simp [ratio, catlin_chi_eq_eight, catlin_sigma_eq_seven]

theorem catlin_ratio_gt_one : 1 < ratio graph := by
  rw [catlin_ratio_eq]
  norm_num

def UniversalRatioBound (C : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), 2 ≤ Fintype.card V →
    ratio G ≤ C * (Real.sqrt (Fintype.card V : ℝ) / Real.log (Fintype.card V : ℝ))

theorem exists_universal_ratio_bound : ∃ C : ℝ, 0 < C ∧ UniversalRatioBound C := by
  obtain ⟨C, hC, h⟩ := Erdos717.erdos_717
  refine ⟨C, hC, ?_⟩
  intro V _ G hn
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hσ : (0 : ℝ) < Erdos717.cliqueSubdivisionNumber G := by
    exact_mod_cast (Erdos717.one_le_cliqueSubdivisionNumber G)
  exact (div_le_iff₀ hσ).mpr (h V G hn)

noncomputable def extremalRatio (n : ℕ) : ℝ :=
  sSup (Set.range fun G : SimpleGraph (Fin n) => ratio G)

theorem ratio_range_bddAbove {n : ℕ} (hn : 2 ≤ n) :
    BddAbove (Set.range fun G : SimpleGraph (Fin n) => ratio G) := by
  obtain ⟨C, _, hC⟩ := exists_universal_ratio_bound
  refine ⟨C * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)), ?_⟩
  rintro y ⟨G, rfl⟩
  simpa only [Fintype.card_fin] using hC (Fin n) G (by simpa using hn)

theorem extremal_upper_bound {C : ℝ} (hC : UniversalRatioBound C)
    {n : ℕ} (hn : 2 ≤ n) :
    extremalRatio n ≤ C * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)) := by
  apply csSup_le (Set.range_nonempty (fun G : SimpleGraph (Fin n) => ratio G))
  rintro y ⟨G, rfl⟩
  simpa only [Fintype.card_fin] using hC (Fin n) G (by simpa using hn)

theorem catlin_extremal_lower_bound : (8 / 7 : ℝ) ≤ extremalRatio 15 := by
  rw [← catlin_ratio_eq]
  exact le_csSup (ratio_range_bddAbove (by norm_num : 2 ≤ 15)) ⟨graph, rfl⟩

theorem catlin_constant_lower_bound {C : ℝ} (hC : UniversalRatioBound C) :
    (8 / 7 : ℝ) * Real.log 15 / Real.sqrt 15 ≤ C := by
  have h := hC Vertex graph (by decide)
  change ratio graph ≤ C * (Real.sqrt 15 / Real.log 15) at h
  rw [catlin_ratio_eq, ← mul_div_assoc] at h
  have hl : 0 < Real.log (15 : ℝ) := Real.log_pos (by norm_num)
  have hs : 0 < Real.sqrt (15 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  exact (div_le_iff₀ hs).mpr ((le_div_iff₀ hl).mp h)

/-- Complete general upper bound, together with our exact finite witness,
its extremal consequence, and its constraint on every universal constant. -/
theorem jsp_000585 :
    ∃ C : ℝ, 0 < C ∧ UniversalRatioBound C ∧
      (∀ n : ℕ, 2 ≤ n →
        extremalRatio n ≤ C * (Real.sqrt (n : ℝ) / Real.log (n : ℝ))) ∧
      (8 / 7 : ℝ) * Real.log 15 / Real.sqrt 15 ≤ C ∧
      graph.chromaticNumber = 8 ∧
      (∀ r, CatlinComplete.ContainsCliqueSubdivision r ↔ r ≤ 7) ∧
      (8 / 7 : ℝ) ≤ extremalRatio 15 := by
  obtain ⟨C, hC, h⟩ := exists_universal_ratio_bound
  exact ⟨C, hC, h, fun _ hn => extremal_upper_bound h hn,
    catlin_constant_lower_bound h, chromaticNumber_eq_eight,
    CatlinComplete.containsCliqueSubdivision_iff, catlin_extremal_lower_bound⟩

end JSP000585
