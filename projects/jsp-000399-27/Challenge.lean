import JSP000399Triple

/- Independently stated interface, matching the inspected original definitions. -/
namespace StatementComparison

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k card : ℕ) : Prop :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card →
    sumMultiset A k = sumMultiset B k → A = B

example : ¬ Erdos494Unique 3 27 :=
  JSP000399Triple.not_unique_27_triples

example : ∃ A B : Finset ℂ, A.card = 27 ∧ B.card = 27 ∧ A ≠ B ∧
    (A.powersetCard 3).val.map (fun s => s.sum id) =
      (B.powersetCard 3).val.map (fun s => s.sum id) := by
  obtain ⟨A, B, hA, hB, hs, hne⟩ := JSP000399Triple.complex_counterexample
  exact ⟨A, B, hA, hB, hne, hs⟩

end StatementComparison
