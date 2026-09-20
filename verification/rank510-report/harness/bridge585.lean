import JSP000585Complete

namespace Verify585

-- Auditor-defined graph paths: every unordered branch pair has a simple path,
-- interiors avoid every branch vertex and are pairwise disjoint.
structure Subdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : {p : Fin r × Fin r // p.1 < p.2},
    G.Walk (branch e.val.1) (branch e.val.2)
  simple : ∀ e, (path e).IsPath
  avoids : ∀ e, Disjoint
    {x | x ∈ (path e).support ∧ x ≠ branch e.val.1 ∧ x ≠ branch e.val.2}
    (Set.range branch)
  disjoint : Pairwise fun e f => Disjoint
    {x | x ∈ (path e).support ∧ x ≠ branch e.val.1 ∧ x ≠ branch e.val.2}
    {x | x ∈ (path f).support ∧ x ≠ branch f.val.1 ∧ x ≠ branch f.val.2}

def Contains {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (Subdivision G r)

theorem subdivision_iff {V : Type*} (G : SimpleGraph V) (r : ℕ) :
    Contains G r ↔ Erdos717.ContainsCliqueSubdivision G r := by
  constructor
  · rintro ⟨S⟩
    exact ⟨{
      branch := S.branch
      path := S.path
      path_isPath := S.simple
      interior_avoids_branch := S.avoids
      interior_pairwise := S.disjoint
    }⟩
  · rintro ⟨S⟩
    exact ⟨{
      branch := S.branch
      path := S.path
      simple := S.path_isPath
      avoids := S.interior_avoids_branch
      disjoint := S.interior_pairwise
    }⟩

theorem sigma_spec {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Contains G (Erdos717.cliqueSubdivisionNumber G) ∧
      ∀ r : ℕ, Contains G r → r ≤ Erdos717.cliqueSubdivisionNumber G := by
  refine ⟨(subdivision_iff G _).mpr
    (Erdos717.containsCliqueSubdivision_cliqueSubdivisionNumber G), ?_⟩
  intro r hr
  exact Erdos717.le_cliqueSubdivisionNumber ((subdivision_iff G r).mp hr)

-- The constant is chosen before the graph, vertex type and cardinality.
-- The denominator is a positive attained maximum, not an arbitrary proxy.
theorem uniform_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      2 ≤ Fintype.card V → ∃ s : ℕ, 0 < s ∧ Contains G s ∧
        (∀ r : ℕ, Contains G r → r ≤ s) ∧
        (G.chromaticNumber.toNat : ℝ) / (s : ℝ) ≤
          C * (Real.sqrt (Fintype.card V : ℝ) / Real.log (Fintype.card V : ℝ)) := by
  obtain ⟨C, hC, h⟩ := JSP000585.exists_universal_ratio_bound
  refine ⟨C, hC, ?_⟩
  intro V _ G hn
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hmax := sigma_spec G
  refine ⟨Erdos717.cliqueSubdivisionNumber G, ?_, hmax.1, hmax.2, ?_⟩
  · exact lt_of_lt_of_le (by decide : 0 < 1)
      (Erdos717.one_le_cliqueSubdivisionNumber G)
  · simpa only [JSP000585.ratio, Erdos717.chiNat] using h V G hn

theorem catlin_exact :
    CatlinComplete.graph.chromaticNumber = 8 ∧
      ∀ r : ℕ, Contains CatlinComplete.graph r ↔ r ≤ 7 := by
  refine ⟨CatlinComplete.chromaticNumber_eq_eight, ?_⟩
  intro r
  exact (subdivision_iff _ r).trans (JSP000585.catlin_subdivision_iff r)

end Verify585
