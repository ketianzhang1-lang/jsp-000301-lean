/-
Copyright 2026 Ketian Zhang. Licensed under Apache-2.0.
Prepared with OpenAI Codex. The main mathematical dependency is the credited
Erdos548.tree_free_edge_bound, supplied in Upstream548.lean.
-/
import Upstream548
import RamseyDefinitions

namespace JSP000438

lemma edge_count_add_compl {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard + Gᶜ.edgeSet.ncard = (Fintype.card V).choose 2 := by
  classical
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hu : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    apply Finset.coe_injective
    simp only [Finset.coe_union, SimpleGraph.coe_edgeFinset]
    rw [← SimpleGraph.edgeSet_sup, sup_compl_eq_top]
  calc
    G.edgeSet.ncard + Gᶜ.edgeSet.ncard = G.edgeFinset.card + Gᶜ.edgeFinset.card := by
      simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.ncard_eq_toFinset_card']
    _ = (G.edgeFinset ∪ Gᶜ.edgeFinset).card := (Finset.card_union_of_disjoint hd).symm
    _ = (Fintype.card V).choose 2 := by
      rw [hu, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

lemma twice_choose_two (N : ℕ) : 2 * N.choose 2 = N * (N - 1) := by
  rw [Nat.choose_two_right, mul_comm, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self N)]

/-- Every red/blue complete graph of order `m+n-2` contains a red copy of
the `m`-vertex tree `T` or a blue copy of the `n`-vertex tree `S`. -/
theorem trees_monochromatic (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (T : SimpleGraph (Fin m)) (S : SimpleGraph (Fin n))
    (hT : T.IsTree) (hS : S.IsTree) (G : SimpleGraph (Fin (m + n - 2))) :
    T.IsContained G ∨ S.IsContained Gᶜ := by
  classical
  by_contra h
  have hN : 0 < m + n - 2 := by omega
  have hred := Erdos548.tree_free_edge_bound T hT (by simpa using hm) G
    (by simpa using hN) (fun hc => h (Or.inl hc))
  have hblue := Erdos548.tree_free_edge_bound S hS (by simpa using hn) Gᶜ
    (by simpa using hN) (fun hc => h (Or.inr hc))
  have htotal := edge_count_add_compl G
  simp only [Fintype.card_fin] at hred hblue htotal
  have hchoose := twice_choose_two (m + n - 2)
  have hstrict : (m - 2) + (n - 2) < (m + n - 2) - 1 := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hstrict hN
  nlinarith

/-- Direct coloring statement for every tree order `n ≥ 2`. -/
theorem tree_monochromatic (n : ℕ) (hn : 2 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    : ∀ G : SimpleGraph (Fin (2 * n - 2)), T.IsContained G ∨ T.IsContained Gᶜ := by
  rw [show 2 * n - 2 = n + n - 2 by omega]
  exact trees_monochromatic n n hn hn T T hT hT

/-- An asymmetric Ramsey-number consequence, with no asymptotic qualifier. -/
theorem graphRamsey_trees (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (T : SimpleGraph (Fin m)) (S : SimpleGraph (Fin n))
    (hT : T.IsTree) (hS : S.IsTree) : SimpleGraph.graphRamsey T S ≤ m + n - 2 := by
  exact Nat.sInf_le (trees_monochromatic m n hm hn T S hT hS)

end JSP000438

namespace Erdos547

set_option linter.unusedVariables false in
/-- The full corrected statement of Erdős 547 / JSP-000438, as stated in
FormalConjectures/ErdosProblems/547.lean. In particular, all `n ≥ 2` occur. -/
theorem erdos_547 :
    ∀ (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)),
      T.IsTree → SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2 := by
  intro n hn T hT
  exact Nat.sInf_le (JSP000438.tree_monochromatic n hn T hT)

end Erdos547
