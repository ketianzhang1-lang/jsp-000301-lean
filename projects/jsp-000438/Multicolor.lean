/-
Copyright 2026 Ketian Zhang. Licensed under Apache-2.0.
Prepared with OpenAI Codex. This is a finite-color consequence of the
credited Erdős–Sós formalization in Upstream548.lean, not new mathematics.
-/
import JSP000438

open scoped BigOperators

namespace JSP000438

/-- A finite family of graphs covering all edges has total edge count at least
the edge count of the complete graph. Overlaps are permitted. -/
lemma sum_edges_of_cover {C V : Type} [Fintype C] [Fintype V]
    (G : C → SimpleGraph V) (hcover : (⨆ c, G c) = ⊤) :
    (Fintype.card V).choose 2 ≤ ∑ c, (G c).edgeSet.ncard := by
  classical
  have hu : Finset.univ.biUnion (fun c => (G c).edgeFinset) =
      (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      SimpleGraph.mem_edgeFinset]
    rw [← Set.mem_iUnion, ← SimpleGraph.edgeSet_iSup, hcover]
  calc
    (Fintype.card V).choose 2 = (⊤ : SimpleGraph V).edgeFinset.card :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two.symm
    _ = (Finset.univ.biUnion (fun c => (G c).edgeFinset)).card := by rw [hu]
    _ ≤ ∑ c, (G c).edgeFinset.card := Finset.card_biUnion_le
    _ = ∑ c, (G c).edgeSet.ncard := by
      simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.ncard_eq_toFinset_card']

/-- The finite-color tree Ramsey bound in a graph-cover interface.
For each color `c`, prescribe a tree of order `m c ≥ 2`. At
`2 + ∑ c, (m c - 2)` vertices, some color contains its prescribed tree.
The color classes may even overlap; only coverage is required. -/
theorem multicolor_trees_monochromatic {C : Type} [Fintype C]
    (m : C → ℕ) (hm : ∀ c, 2 ≤ m c)
    (T : (c : C) → SimpleGraph (Fin (m c))) (hT : ∀ c, (T c).IsTree)
    (G : C → SimpleGraph (Fin ((∑ c, (m c - 2)) + 2)))
    (hcover : (⨆ c, G c) = ⊤) :
    ∃ c, (T c).IsContained (G c) := by
  classical
  by_contra h
  have hN : 0 < (∑ c, (m c - 2)) + 2 := by omega
  have hfree : ∀ c, ¬(T c).IsContained (G c) := by
    intro c hc
    exact h ⟨c, hc⟩
  have hb : ∀ c, 2 * (G c).edgeSet.ncard ≤
      (m c - 2) * ((∑ c, (m c - 2)) + 2) := by
    intro c
    simpa only [Fintype.card_fin] using
      Erdos548.tree_free_edge_bound (T c) (hT c) (by simpa using hm c)
        (G c) (by simp) (hfree c)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hb c)
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hs
  have hc := sum_edges_of_cover G hcover
  simp only [Fintype.card_fin] at hc
  have hchoose := twice_choose_two ((∑ c, (m c - 2)) + 2)
  have hpred : ((∑ c, (m c - 2)) + 2) - 1 = (∑ c, (m c - 2)) + 1 := by omega
  rw [hpred] at hchoose
  nlinarith

/-- The graph consisting of the edges of one color. Values assigned to
diagonal pairs are ignored, since `fromEdgeSet` removes loops. -/
def edgeColorGraph {C V : Type} (χ : Sym2 V → C) (c : C) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | χ e = c}

/-- The same bound for an actual coloring of unordered pairs, expressed using
an injective vertex map and an explicit monochromatic adjacency condition. -/
theorem multicolor_tree_embedding {C : Type} [Fintype C]
    (m : C → ℕ) (hm : ∀ c, 2 ≤ m c)
    (T : (c : C) → SimpleGraph (Fin (m c))) (hT : ∀ c, (T c).IsTree)
    (χ : Sym2 (Fin ((∑ c, (m c - 2)) + 2)) → C) :
    ∃ c, ∃ f : Fin (m c) ↪ Fin ((∑ c, (m c - 2)) + 2),
      ∀ a b, (T c).Adj a b → χ s(f a, f b) = c := by
  have hcover : (⨆ c, edgeColorGraph χ c) = ⊤ := by
    ext a b
    simp [edgeColorGraph, SimpleGraph.iSup_adj]
  obtain ⟨c, ⟨f⟩⟩ := multicolor_trees_monochromatic m hm T hT
    (edgeColorGraph χ) hcover
  refine ⟨c, ⟨f, f.injective⟩, ?_⟩
  intro a b hab
  exact (f.toHom.map_adj hab).1

/-- A finite-color Ramsey number for a family of trees or other graphs.
The result below separately supplies a member of this defining set, so its
upper bound does not exploit the infimum of an empty set. -/
noncomputable def multicolorGraphRamsey {C : Type} [Fintype C]
    (m : C → ℕ) (T : (c : C) → SimpleGraph (Fin (m c))) : ℕ :=
  sInf {N : ℕ | ∀ χ : Sym2 (Fin N) → C,
    ∃ c, ∃ f : Fin (m c) ↪ Fin N,
      ∀ a b, (T c).Adj a b → χ s(f a, f b) = c}

/-- For prescribed trees of orders `m c ≥ 2`,
`R((T c)_c) ≤ 2 + ∑ c, (m c - 2)`. -/
theorem multicolorGraphRamsey_trees {C : Type} [Fintype C] [Nonempty C]
    (m : C → ℕ) (hm : ∀ c, 2 ≤ m c)
    (T : (c : C) → SimpleGraph (Fin (m c))) (hT : ∀ c, (T c).IsTree) :
    multicolorGraphRamsey m T ≤ (∑ c, (m c - 2)) + 2 := by
  exact Nat.sInf_le (multicolor_tree_embedding m hm T hT)

end JSP000438
