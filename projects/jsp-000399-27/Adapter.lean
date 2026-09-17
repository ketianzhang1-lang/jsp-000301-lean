import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Int.Interval
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

/-- Remove the proof-carrying finite-subset layer before finite computation. -/
theorem intSumMultiset_eq_map_sum (A : Finset ℤ) (k : ℕ) :
    intSumMultiset A k = (A.val.powersetCard k).map Multiset.sum := by
  unfold intSumMultiset
  rw [← Finset.map_val_val_powersetCard A k]
  simp only [Multiset.map_map, Function.comp_def, Finset.sum_val]

/-- Finite support and exact multiplicities certify multiset equality. -/
theorem intSumMultiset_eq_of_counts {A B : Finset ℤ} {k : ℕ}
    (S : Finset ℤ)
    (hA : ∀ z ∈ intSumMultiset A k, z ∈ S)
    (hB : ∀ z ∈ intSumMultiset B k, z ∈ S)
    (hc : ∀ z ∈ S,
      (intSumMultiset A k).count z = (intSumMultiset B k).count z) :
    intSumMultiset A k = intSumMultiset B k := by
  apply Multiset.ext.mpr
  intro z
  by_cases hz : z ∈ S
  · exact hc z hz
  · have hza : z ∉ intSumMultiset A k := fun h => hz (hA z h)
    have hzb : z ∉ intSumMultiset B k := fun h => hz (hB z h)
    rw [Multiset.count_eq_zero.mpr hza, Multiset.count_eq_zero.mpr hzb]

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
