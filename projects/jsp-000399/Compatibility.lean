import JSP000399

/-!
Statement-only compatibility adapter. Definitions below reproduce the
Formal Conjectures 494 specification at 40e7c98697de6f66b8cbdbf641749ab39ed9c152.
Copyright 2025 The Formal Conjectures Authors; Apache-2.0.
-/
namespace Erdos494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card →
    sumMultiset A k = sumMultiset B k → A = B

/-- The genuine exception at cardinality 27. -/
theorem card_27_counterexample : ¬ Erdos494Unique 3 27 := by
  exact JSP000399.not_unique_27

end Erdos494
