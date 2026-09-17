import JSP000476
open JSP000476

-- The old sufficient condition k² < p fails here, but the exact criterion succeeds.
example : SquareSumFree (multiples 11 4) := by
  rw [prime_multiples_iff (by norm_num : Nat.Prime 11)]
  norm_num

-- Equality is excluded: {3,6} sums to 9.
example : ¬ SquareSumFree (multiples 3 2) := by
  rw [prime_multiples_iff (by norm_num : Nat.Prime 3)]
  norm_num

-- Composite squarefree multipliers are covered as well.
example : SquareSumFree (multiples 30 7) := by
  have h30 : Squarefree 30 := by
    change Squarefree (2 * (3 * 5))
    rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
    exact ⟨by decide, Nat.prime_two.squarefree, by decide,
      (by norm_num : Nat.Prime 3).squarefree, (by norm_num : Nat.Prime 5).squarefree⟩
  rw [squareSumFree_multiples_iff h30, triangular_eq]
  norm_num

-- The squarefree part, not m itself, determines the threshold: 12 = 2² * 3.
example : ¬ SquareSumFree (multiples 12 2) := by
  have h := square_part_multiples_iff (k := 2)
    (by norm_num : 0 < (2 : ℕ)) (by norm_num : Nat.Prime 3).squarefree
  norm_num at h
  exact h

example : ∃ A ⊆ Finset.Icc 1 1100, A.card = 10 ∧ SquareSumFree A :=
  exists_card_squareSumFree 10 1100 (by norm_num)
