import JSP000746

namespace Verify746

/-- The source question, with triangle-freeness written as an explicit relation condition. -/
theorem intended (G : SimpleGraph ℤ)
    (htri : ∀ a b c : ℤ, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c)) :
    ∃ a b c : ℤ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ c = a + b ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := by
  apply JSP000746.jsp_000746 G
  intro s hs
  obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  exact htri a b c (SimpleGraph.is3Clique_triple_iff.mp hs)

/-- The stronger positive witness avoids any accidental solution using zero or repetitions. -/
theorem bounded_positive (G : SimpleGraph ℤ) (hG : G.CliqueFree 3) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ a + b ≤ 18 ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a (a + b) ∧ ¬ G.Adj b (a + b) :=
  JSP000746.integer_graph G hG

/-- Fin n is labelled by i.val+1; the sum vertex therefore has value a.val+b.val+1. -/
theorem exact_finite_threshold (n : ℕ) :
    (∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ (a b : Fin n) (hs : a.val + b.val + 1 < n), a.val < b.val ∧
        ¬ G.Adj a b ∧ ¬ G.Adj a ⟨a.val + b.val + 1, hs⟩ ∧
        ¬ G.Adj b ⟨a.val + b.val + 1, hs⟩) ↔ 18 ≤ n :=
  JSP000746Sharp.exact_threshold n

/-- This is the cardinality of the submitted witness's edge list, not an optimal-edge claim. -/
theorem witness_edge_list_length : JSP000746Sharp.edges.length = 43 := by decide

end Verify746
