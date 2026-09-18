import Sharp
import ErdosProblems.Erdos718.Erdos718Core
import Mathlib.Data.Finset.Sort

/-! Our bridge between the original finite branch-set certificates and the
embedding-indexed subdivision model. Reversing a path preserves its interior;
the ordering convention for branch pairs does not change the graph property. -/

namespace JSP000585
open Finset CatlinComplete CatlinCertificates

theorem edge_left_mem {B : Finset Vertex} (e : BranchEdge B) : e.val.1 ∈ B :=
  (mem_product.mp (mem_filter.mp e.property).1).1

theorem edge_right_mem {B : Finset Vertex} (e : BranchEdge B) : e.val.2 ∈ B :=
  (mem_product.mp (mem_filter.mp e.property).1).2

theorem edge_lt {B : Finset Vertex} (e : BranchEdge B) : e.val.1 < e.val.2 :=
  (mem_filter.mp e.property).2

noncomputable def toIndexed {B : Finset Vertex} {r : ℕ}
    (S : Subdivision B) (hB : B.card = r) : Erdos718.CliqueSubdivision graph r := by
  classical
  let b := B.orderEmbOfFin hB
  let edge (e : Erdos718.CliqueEdge r) : BranchEdge B :=
    ⟨(b e.val.1, b e.val.2), mem_filter.mpr ⟨mem_product.mpr
      ⟨B.orderEmbOfFin_mem hB _, B.orderEmbOfFin_mem hB _⟩, b.strictMono e.property⟩⟩
  have hinj : Function.Injective edge := by
    intro e f h
    apply Subtype.ext
    apply Prod.ext
    · exact b.injective (congrArg (fun z : BranchEdge B => z.val.1) h)
    · exact b.injective (congrArg (fun z : BranchEdge B => z.val.2) h)
  refine {
    branch := b.toEmbedding
    path := fun e => S.path (edge e)
    path_isPath := fun e => S.isPath (edge e)
    interior_avoids_branch := ?_
    interior_pairwise := ?_
  }
  · intro e
    apply Set.disjoint_left.mpr
    rintro x hx ⟨i, rfl⟩
    exact (Finset.disjoint_left.mp (S.avoids (edge e)))
      (mem_inside.mpr hx) (B.orderEmbOfFin_mem hB i)
  · intro e f hef
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp (S.pairwise (fun h => hef (hinj h))))
      (mem_inside.mpr hx) (mem_inside.mpr hy)

def branchSet {r : ℕ} (S : Erdos718.CliqueSubdivision graph r) : Finset Vertex :=
  Finset.univ.map S.branch

@[simp] theorem card_branchSet {r : ℕ} (S : Erdos718.CliqueSubdivision graph r) :
    (branchSet S).card = r := by simp [branchSet]

@[simp] theorem mem_branchSet {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (v : Vertex) : v ∈ branchSet S ↔ v ∈ Set.range S.branch := by
  simp [branchSet]

noncomputable def branchLabel {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (v : branchSet S) : Fin r := Classical.choose (Finset.mem_map.mp v.property)

@[simp] theorem branch_branchLabel {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (v : branchSet S) : S.branch (branchLabel S v) = v.val :=
  (Classical.choose_spec (Finset.mem_map.mp v.property)).2

abbrev leftVertex {B : Finset Vertex} (e : BranchEdge B) : B := ⟨e.val.1, edge_left_mem e⟩
abbrev rightVertex {B : Finset Vertex} (e : BranchEdge B) : B := ⟨e.val.2, edge_right_mem e⟩

theorem labels_ne {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (e : BranchEdge (branchSet S)) :
    branchLabel S (leftVertex e) ≠ branchLabel S (rightVertex e) := by
  intro h
  have := congrArg S.branch h
  simp only [branch_branchLabel] at this
  exact (ne_of_lt (edge_lt e)) this

noncomputable def indexedEdge {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (e : BranchEdge (branchSet S)) : Erdos718.CliqueEdge r :=
  if h : branchLabel S (leftVertex e) < branchLabel S (rightVertex e) then
    ⟨(branchLabel S (leftVertex e), branchLabel S (rightVertex e)), h⟩
  else ⟨(branchLabel S (rightVertex e), branchLabel S (leftVertex e)),
    lt_of_le_of_ne (le_of_not_gt h) (labels_ne S e).symm⟩

theorem indexedEdge_injective {r : ℕ} (S : Erdos718.CliqueSubdivision graph r) :
    Function.Injective (indexedEdge S) := by
  intro e f h
  have hu := congrArg (fun z : Erdos718.CliqueEdge r => S.branch z.val.1) h
  have hv := congrArg (fun z : Erdos718.CliqueEdge r => S.branch z.val.2) h
  have he := edge_lt e
  have hf := edge_lt f
  by_cases hE : branchLabel S (leftVertex e) < branchLabel S (rightVertex e)
  · by_cases hF : branchLabel S (leftVertex f) < branchLabel S (rightVertex f)
    · simp only [indexedEdge, dite_eq_left hE, dite_eq_left hF, branch_branchLabel] at hu hv
      exact Subtype.ext (Prod.ext hu hv)
    · simp only [indexedEdge, dite_eq_left hE, dite_eq_right hF, branch_branchLabel] at hu hv
      change e.val.1 = f.val.2 at hu
      change e.val.2 = f.val.1 at hv
      have hrev : e.val.2 < e.val.1 := by
        calc
          e.val.2 = f.val.1 := hv
          _ < f.val.2 := hf
          _ = e.val.1 := hu.symm
      exact (lt_asymm he hrev).elim
  · by_cases hF : branchLabel S (leftVertex f) < branchLabel S (rightVertex f)
    · simp only [indexedEdge, dite_eq_right hE, dite_eq_left hF, branch_branchLabel] at hu hv
      change e.val.2 = f.val.1 at hu
      change e.val.1 = f.val.2 at hv
      have hrev : e.val.2 < e.val.1 := by
        calc
          e.val.2 = f.val.1 := hu
          _ < f.val.2 := hf
          _ = e.val.1 := hv.symm
      exact (lt_asymm he hrev).elim
    · simp only [indexedEdge, dite_eq_right hE, dite_eq_right hF, branch_branchLabel] at hu hv
      exact Subtype.ext (Prod.ext hv hu)

noncomputable def convertedPath {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (e : BranchEdge (branchSet S)) : graph.Walk e.val.1 e.val.2 :=
  if h : branchLabel S (leftVertex e) < branchLabel S (rightVertex e) then
    (S.path ⟨(branchLabel S (leftVertex e), branchLabel S (rightVertex e)), h⟩).copy
      (branch_branchLabel S (leftVertex e)) (branch_branchLabel S (rightVertex e))
  else
    (S.path ⟨(branchLabel S (rightVertex e), branchLabel S (leftVertex e)),
      lt_of_le_of_ne (le_of_not_gt h) (labels_ne S e).symm⟩).reverse.copy
      (branch_branchLabel S (leftVertex e)) (branch_branchLabel S (rightVertex e))

theorem convertedPath_isPath {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (e : BranchEdge (branchSet S)) : (convertedPath S e).IsPath := by
  unfold convertedPath
  split
  · exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr (S.path_isPath _)
  · exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr (S.path_isPath _).reverse

theorem inside_convertedPath {r : ℕ} (S : Erdos718.CliqueSubdivision graph r)
    (e : BranchEdge (branchSet S)) (x : Vertex) :
    x ∈ inside (convertedPath S e) ↔
      x ∈ Erdos718.walkInteriorSet (S.path (indexedEdge S e)) := by
  rw [mem_inside]
  by_cases h : branchLabel S (leftVertex e) < branchLabel S (rightVertex e)
  · rw [convertedPath, dite_eq_left h, indexedEdge, dite_eq_left h]
    rw [SimpleGraph.Walk.support_copy]
    change _ ↔ (x ∈ _ ∧ x ≠ S.branch (branchLabel S (leftVertex e)) ∧
      x ≠ S.branch (branchLabel S (rightVertex e)))
    apply and_congr_right
    intro _
    simp only [branch_branchLabel]
  · rw [convertedPath, dite_eq_right h, indexedEdge, dite_eq_right h]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse, List.mem_reverse]
    change _ ↔ (x ∈ _ ∧ x ≠ S.branch (branchLabel S (rightVertex e)) ∧
      x ≠ S.branch (branchLabel S (leftVertex e)))
    apply and_congr_right
    intro _
    simp only [branch_branchLabel]
    tauto

noncomputable def fromIndexed {r : ℕ} (S : Erdos718.CliqueSubdivision graph r) :
    Subdivision (branchSet S) where
  path := convertedPath S
  isPath := convertedPath_isPath S
  avoids e := by
    apply Finset.disjoint_left.mpr
    intro x hx hB
    exact (Set.disjoint_left.mp (S.interior_avoids_branch (indexedEdge S e)))
      ((inside_convertedPath S e x).mp hx) ((mem_branchSet S x).mp hB)
  pairwise e f hef := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Set.disjoint_left.mp (S.interior_pairwise
      (fun h => hef (indexedEdge_injective S h))))
      ((inside_convertedPath S e x).mp hx) ((inside_convertedPath S f x).mp hy)

theorem containsSubdivision_iff_indexed (r : ℕ) :
    ContainsCliqueSubdivision r ↔ Erdos718.ContainsCliqueSubdivision graph r := by
  constructor
  · rintro ⟨B, hB, ⟨S⟩⟩
    exact ⟨toIndexed S hB⟩
  · rintro ⟨S⟩
    exact ⟨branchSet S, card_branchSet S, ⟨fromIndexed S⟩⟩

end JSP000585
