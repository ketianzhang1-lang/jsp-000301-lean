import PrimePower

#print axioms BoseChowlaPrimePower.exponent_family
#print axioms BoseChowlaPrimePower.prime_power_exponents
#print axioms BoseChowlaPrimePower.IsBhMod.isBh
#print axioms BoseChowlaPrimePower.exists_prime_power_modular
#print axioms BoseChowlaPrimePower.jsp000212_prime_power

example (p r h : ℕ) (hp : p.Prime) (hr : 0 < r) (hh : 2 ≤ h) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 ((p ^ r) ^ h - 1) ∧ A.card = p ^ r ∧
      ∀ s t : Multiset ℕ, s.card = h → t.card = h →
        (∀ a ∈ s, a ∈ A) → (∀ a ∈ t, a ∈ A) →
        s.sum % ((p ^ r) ^ h - 1) = t.sum % ((p ^ r) ^ h - 1) → s = t :=
  BoseChowlaPrimePower.exists_prime_power_modular p r h hp hr hh

example (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 ((p ^ r) ^ 3 - 1) ∧ A.card = p ^ r ∧
      ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = 3 → T.card = 3 →
        S.sum id = T.sum id → S = T :=
  BoseChowlaPrimePower.jsp000212_prime_power p r hp hr

-- Genuine non-prime cardinalities; repetitions and modular equality are retained.
example : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 63 ∧ A.card = 4 ∧
    BoseChowlaPrimePower.IsBhMod 3 63 A := by
  simpa using BoseChowlaPrimePower.exists_prime_power_modular 2 2 3
    (by decide) (by decide) (by decide)

example : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 511 ∧ A.card = 8 ∧
    BoseChowlaPrimePower.IsBhMod 3 511 A := by
  simpa using BoseChowlaPrimePower.exists_prime_power_modular 2 3 3
    (by decide) (by decide) (by decide)

example : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 728 ∧ A.card = 9 ∧
    BoseChowlaPrimePower.IsBhMod 3 728 A := by
  simpa using BoseChowlaPrimePower.exists_prime_power_modular 3 2 3
    (by decide) (by decide) (by decide)

example : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 15 ∧ A.card = 4 ∧
    BoseChowlaPrimePower.IsBhMod 2 15 A := by
  simpa using BoseChowlaPrimePower.exists_prime_power_modular 2 2 2
    (by decide) (by decide) (by decide)
