import Catlin

namespace CatlinComplete
open Finset CatlinCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sevenBranches : Finset Vertex := {0, 1, 2, 3, 4, 5, 6}

theorem seven_exceptional : ∀ e : BranchEdge sevenBranches,
    ¬ adjacent e.val.1 e.val.2 → e.val.1.val < 3 ∧ e.val.2 = 6 := by
  decide +kernel

theorem seven_detour : ∀ u : Vertex, u.val < 3 →
    graph.Adj u (u + 12) ∧ graph.Adj (u + 12) (u + 9) ∧
      graph.Adj (u + 9) 6 := by decide

def sevenPath (e : BranchEdge sevenBranches) : graph.Walk e.val.1 e.val.2 := by
  by_cases h : adjacent e.val.1 e.val.2
  · exact .cons h .nil
  · have he := seven_exceptional e h
    have hd := seven_detour e.val.1 he.1
    rw [he.2]
    exact .cons hd.1 (.cons hd.2.1 (.cons hd.2.2 .nil))

def sevenSubdivision : Subdivision sevenBranches where
  path := sevenPath
  isPath := by
    intro e
    apply SimpleGraph.Walk.IsPath.mk'
    have h : ∀ e : BranchEdge sevenBranches, (sevenPath e).support.Nodup := by
      decide +kernel
    exact h e
  avoids := by decide +kernel
  pairwise := by
    change ∀ e f : BranchEdge sevenBranches, e ≠ f →
      Disjoint (inside (sevenPath e)) (inside (sevenPath f))
    decide +kernel

theorem contains_K7_subdivision : ContainsCliqueSubdivision 7 :=
  ⟨sevenBranches, by decide, ⟨sevenSubdivision⟩⟩

/-- Restriction retains the paths indexed by pairs in the smaller branch set. -/
def branchEdgeInclusion {A B : Finset Vertex} (h : A ⊆ B) :
    BranchEdge A ↪ BranchEdge B where
  toFun e := ⟨e.val, by
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp e.property
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h hu, h hv⟩, hlt⟩⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact congrArg (fun z : BranchEdge B => z.val) hef

def Subdivision.restrict {A B : Finset Vertex} (S : Subdivision B) (h : A ⊆ B) :
    Subdivision A where
  path e := S.path (branchEdgeInclusion h e)
  isPath e := S.isPath (branchEdgeInclusion h e)
  avoids e := Finset.disjoint_of_subset_right h (S.avoids (branchEdgeInclusion h e))
  pairwise _e _f hef := S.pairwise (fun he => hef ((branchEdgeInclusion h).injective he))

theorem containsCliqueSubdivision_antitone {r s : ℕ} (hrs : r ≤ s)
    (hs : ContainsCliqueSubdivision s) : ContainsCliqueSubdivision r := by
  obtain ⟨B, hB, ⟨S⟩⟩ := hs
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq (hrs.trans_eq hB.symm)
  exact ⟨A, hA, ⟨S.restrict hAB⟩⟩

/-- Exact classification of all clique-subdivision orders in the explicit graph. -/
theorem containsCliqueSubdivision_iff (r : ℕ) :
    ContainsCliqueSubdivision r ↔ r ≤ 7 := by
  constructor
  · intro hr
    by_contra hn
    exact no_K8_subdivision (containsCliqueSubdivision_antitone (by omega) hr)
  · intro hr
    exact containsCliqueSubdivision_antitone hr contains_K7_subdivision

theorem sharp_catlin_counterexample :
    graph.chromaticNumber = 8 ∧ ∀ r : ℕ, (ContainsCliqueSubdivision r ↔ r ≤ 7) :=
  ⟨chromaticNumber_eq_eight, containsCliqueSubdivision_iff⟩

#print axioms contains_K7_subdivision
#print axioms containsCliqueSubdivision_antitone
#print axioms sharp_catlin_counterexample

end CatlinComplete
