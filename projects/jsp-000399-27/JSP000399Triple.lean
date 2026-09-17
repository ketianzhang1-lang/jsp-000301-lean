import Adapter

/-!
# The exceptional cardinality 27 for reconstruction from three-element sums

This is a finite explicit witness to the known negative result at n=27, k=3.
The exceptional cardinality is classical (Fomin--Izhboldin, 1994).
The explicit distinct-integer witness below was constructed and checked with
OpenAI ChatGPT during preparation of this package.
It does not claim the complete classification of the original problem.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace JSP000399Triple

def witness : Finset ℤ :=
  {-20, -19, -15, -13, -11, -10, -8, -7, -6, -5, -3, -2, -1,
    0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 15, 18, 21}

def reflected : Finset ℤ := witness.image (fun x => -x)

theorem witness_card : witness.card = 27 := by decide +kernel

theorem reflected_card : reflected.card = 27 := by decide +kernel

theorem witness_ne_reflected : witness ≠ reflected := by decide +kernel

theorem equal_triple_sums :
    intSumMultiset witness 3 = intSumMultiset reflected 3 := by
  apply intSumMultiset_eq_of_counts (Finset.Icc (-54) 54)
  · simp only [Finset.mem_Icc, intSumMultiset_eq_map_sum]
    decide +kernel
  · simp only [Finset.mem_Icc, intSumMultiset_eq_map_sum]
    decide +kernel
  · simp only [intSumMultiset_eq_map_sum]
    decide +kernel

theorem complex_counterexample :
    ∃ A B : Finset ℂ, A.card = 27 ∧ B.card = 27 ∧
      complexSumMultiset A 3 = complexSumMultiset B 3 ∧ A ≠ B :=
  lift_integer_counterexample witness_card reflected_card
    witness_ne_reflected equal_triple_sums

def UniqueRecovery (k n : ℕ) : Prop :=
  ∀ A B : Finset ℂ, A.card = n → B.card = n →
    complexSumMultiset A k = complexSumMultiset B k → A = B

theorem not_unique_27_triples : ¬ UniqueRecovery 3 27 := by
  intro h
  obtain ⟨A, B, hA, hB, hs, hne⟩ := complex_counterexample
  exact hne (h A B hA hB hs)

end JSP000399Triple
