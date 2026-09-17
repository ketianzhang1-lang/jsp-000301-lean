import GraphCore

namespace CatlinComplete
open Finset CatlinCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One orientation of each unordered pair of distinct branch vertices. -/
def edgeSet (B : Finset Vertex) : Finset (Vertex × Vertex) :=
  (B ×ˢ B).filter fun e => e.1 < e.2

abbrev BranchEdge (B : Finset Vertex) := ↥(edgeSet B)

/-- A literal clique subdivision: simple paths for all branch pairs,
    disjoint interiors, and no branch vertex in an interior. -/
structure Subdivision (B : Finset Vertex) where
  path : ∀ e : BranchEdge B, graph.Walk e.val.1 e.val.2
  isPath : ∀ e, (path e).IsPath
  avoids : ∀ e, Disjoint (inside (path e)) B
  pairwise : Pairwise fun e f => Disjoint (inside (path e)) (inside (path f))

/-- The graph contains a subdivision of the complete graph on r vertices. -/
def ContainsCliqueSubdivision (r : ℕ) : Prop :=
  ∃ B : Finset Vertex, B.card = r ∧ Nonempty (Subdivision B)

theorem sum_demand_edges (B : Finset Vertex) :
    (∑ e : BranchEdge B, demand B e.val.1 e.val.2) = budget B := by
  rw [Finset.sum_coe_sort (edgeSet B) (fun e : Vertex × Vertex => demand B e.1 e.2)]
  unfold edgeSet
  rw [Finset.sum_filter, Finset.sum_product]
  have hinner : ∀ u ∈ B, ∑ v ∈ B, (if u < v then demand B u v else 0) =
      ∑ v, demand B u v := by
    intro u hu
    have hz : ∀ v, (if u < v then demand B u v else 0) = demand B u v := by
      intro v
      by_cases h : u < v <;> simp [h, demand]
    simp_rw [hz]
    exact Finset.sum_subset (Finset.subset_univ B) (by
      intro v _ hv
      simp [demand, hv])
  simp only at hinner ⊢
  simp_rw [Finset.sum_congr rfl hinner]
  unfold budget
  exact Finset.sum_subset (Finset.subset_univ B) (by
    intro u _ hu
    simp [demand, hu])

theorem total_inside_bound {B : Finset Vertex} (S : Subdivision B) :
    (∑ e : BranchEdge B, (inside (S.path e)).card) + B.card ≤ 15 := by
  let U : Finset Vertex := univ.biUnion fun e : BranchEdge B => inside (S.path e)
  have hcardU : U.card = ∑ e : BranchEdge B, (inside (S.path e)).card := by
    apply Finset.card_biUnion
    intro e _ f _ hef
    exact S.pairwise hef
  have hd : Disjoint U B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.disjoint_left.mp (S.avoids e)) he hxB
  have hle := Finset.card_le_card (Finset.subset_univ (U ∪ B))
  rw [Finset.card_union_of_disjoint hd, hcardU] at hle
  simpa using hle

theorem subdivision_budget_bound {B : Finset Vertex} (S : Subdivision B) :
    budget B + B.card ≤ 15 := by
  have hd : budget B ≤ ∑ e : BranchEdge B, (inside (S.path e)).card := by
    rw [← sum_demand_edges B]
    apply Finset.sum_le_sum
    intro e _
    have he : e.val.1 < e.val.2 := (Finset.mem_filter.mp e.property).2
    exact demand_le_inside (S.path e) (S.isPath e) he (S.avoids e)
  exact (Nat.add_le_add_right hd B.card).trans (total_inside_bound S)

end CatlinComplete
