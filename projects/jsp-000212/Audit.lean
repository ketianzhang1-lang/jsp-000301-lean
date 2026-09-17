import BoseChowla

#print axioms BoseChowla.product_injective
#print axioms BoseChowla.sub_ne_zero
#print axioms BoseChowla.exists_exponent_family
#print axioms BoseChowla.exists_bose_chowla
#print axioms BoseChowla.jsp000212

example (p : ℕ) (hp : p.Prime) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p ^ 3 - 1) ∧ A.card = p ∧
      ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = 3 → T.card = 3 →
        S.sum id = T.sum id → S = T :=
  BoseChowla.jsp000212 p hp

example : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 26 ∧ A.card = 3 ∧
    BoseChowla.IsBh 3 A := by
  simpa using BoseChowla.exists_bose_chowla 3 3 (by decide) (by decide)

example : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 124 ∧ A.card = 5 ∧
    BoseChowla.IsBh 3 A := by
  simpa using BoseChowla.exists_bose_chowla 5 3 (by decide) (by decide)
