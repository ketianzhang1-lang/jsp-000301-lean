import StarSharpness

namespace Verify438

-- Standard graph containment and the actual graph complement specify the target.
theorem direct (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (ht : T.IsTree) :
    ∀ G : SimpleGraph (Fin (2*n-2)), T.IsContained G ∨ T.IsContained Gᶜ :=
  JSP000438.tree_monochromatic n hn T ht

-- Spell out the infimum set instead of trusting a renamed Ramsey definition.
theorem intended (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (ht : T.IsTree) :
    sInf {N : ℕ | ∀ G : SimpleGraph (Fin N), T.IsContained G ∨ T.IsContained Gᶜ}
      ≤ 2*n-2 := by
  exact Nat.sInf_le (direct n hn T ht)

theorem sharp (k : ℕ) :
    sInf {N : ℕ | ∀ G : SimpleGraph (Fin N),
      (SimpleGraph.starGraph (0 : Fin (2*k+2))).IsContained G ∨
      (SimpleGraph.starGraph (0 : Fin (2*k+2))).IsContained Gᶜ} = 4*k+2 :=
  JSP000438.star_ramsey_even_order k

end Verify438
