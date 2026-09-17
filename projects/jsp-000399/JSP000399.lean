import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
A 27-element counterexample to recovery from triple sums.
The exceptional cardinality 27 is due to Fomin and Izhboldin (1994).
This independently constructed integer instance does not claim new mathematics.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JSP000399

def A : Finset ℕ := {20, 28, 32, 34, 35, 67, 70, 71, 73, 77, 85, 103, 105, 106, 109, 110, 112, 117, 118, 120, 124, 148, 156, 160, 162, 163, 195}
def B : Finset ℕ := {5, 37, 38, 40, 44, 52, 76, 80, 82, 83, 88, 90, 91, 94, 95, 97, 115, 123, 127, 129, 130, 133, 165, 166, 168, 172, 180}

def natSums (S : Finset ℕ) (k : ℕ) : Multiset ℕ :=
  (S.powersetCard k).val.map fun T => T.sum id

theorem card_A : A.card = 27 := by decide +kernel
theorem card_B : B.card = 27 := by decide +kernel
theorem A_ne_B : A ≠ B := by decide +kernel

theorem equal_triple_sums_nat : natSums A 3 = natSums B 3 := by
  decide +kernel

noncomputable def complexEmbedding : ℕ ↪ ℂ :=
  ⟨fun n => (n : ℂ), Nat.cast_injective⟩

noncomputable def sumMultiset (S : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (S.powersetCard k).val.map fun T => T.sum id

def Unique (k card : ℕ) : Prop :=
  ∀ S T : Finset ℂ, S.card = card → T.card = card →
    sumMultiset S k = sumMultiset T k → S = T

theorem sums_lift (S : Finset ℕ) (k : ℕ) :
    sumMultiset (S.map complexEmbedding) k =
      (natSums S k).map fun n : ℕ => (n : ℂ) := by
  classical
  unfold sumMultiset natSums
  rw [Finset.powersetCard_map, Finset.map_val]
  simp only [Multiset.map_map, Function.comp_apply]
  congr 1
  funext T
  simp [Finset.sum_map, complexEmbedding, Nat.cast_sum]

theorem not_unique_27 : ¬ Unique 3 27 := by
  intro h
  have hA : (A.map complexEmbedding).card = 27 := by simpa using card_A
  have hB : (B.map complexEmbedding).card = 27 := by simpa using card_B
  have hs : sumMultiset (A.map complexEmbedding) 3 =
      sumMultiset (B.map complexEmbedding) 3 := by
    rw [sums_lift, sums_lift, equal_triple_sums_nat]
  have he := h _ _ hA hB hs
  exact A_ne_B (Finset.map_injective complexEmbedding he)

end JSP000399
