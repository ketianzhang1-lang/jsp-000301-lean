import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic

/-!
Transport of exact integer subset-sum certificates to finite subsets of the
complex numbers, preserving every multiplicity.  The complex definition is the
one used by the Formal Conjectures statement of Erdős Problem 494.
-/

namespace JSP000399Triple

def intSumMultiset (A : Finset ℤ) (k : ℕ) : Multiset ℤ :=
  (A.powersetCard k).val.map fun s => s.sum id

/-- Sorting is used only to make a kernel-checked finite certificate efficient. -/
theorem intSumMultiset_eq_of_sort_eq {A B : Finset ℤ} {k : ℕ}
    (h : (intSumMultiset A k).sort (· ≤ ·) =
      (intSumMultiset B k).sort (· ≤ ·)) :
    intSumMultiset A k = intSumMultiset B k := by
  have hm := congrArg (fun l : List ℤ => (l : Multiset ℤ)) h
  simpa using hm

noncomputable def complexSumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def intToComplex : ℤ ↪ ℂ :=
  ⟨fun z => (z : ℂ), Int.cast_injective⟩

def complexify (A : Finset ℤ) : Finset ℂ :=
  A.map intToComplex

@[simp] theorem card_complexify (A : Finset ℤ) :
    (complexify A).card = A.card := by
  exact Finset.card_map _

theorem complexify_injective : Function.Injective complexify :=
  Finset.map_injective intToComplex

theorem complexSumMultiset_complexify (A : Finset ℤ) (k : ℕ) :
    complexSumMultiset (complexify A) k =
      (intSumMultiset A k).map (fun z : ℤ => (z : ℂ)) := by
  unfold complexSumMultiset complexify intSumMultiset
  rw [Finset.powersetCard_map]
  simp only [Finset.map_val, Multiset.map_map]
  congr 1
  funext s
  simp [Finset.sum_map, intToComplex, Int.cast_sum]

theorem lift_integer_counterexample {A B : Finset ℤ} {k n : ℕ}
    (hA : A.card = n) (hB : B.card = n) (hne : A ≠ B)
    (hsum : intSumMultiset A k = intSumMultiset B k) :
    ∃ A B : Finset ℂ, A.card = n ∧ B.card = n ∧
      complexSumMultiset A k = complexSumMultiset B k ∧ A ≠ B := by
  refine ⟨complexify A, complexify B, ?_, ?_, ?_, ?_⟩
  · simpa using hA
  · simpa using hB
  · rw [complexSumMultiset_complexify, complexSumMultiset_complexify, hsum]
  · exact fun h => hne (complexify_injective h)

end JSP000399Triple
