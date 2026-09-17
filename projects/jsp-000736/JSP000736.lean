/-
Copyright 2026 The Formal Conjectures Authors (factorDifferenceSet definition and target statement).
Copyright 2026 the submitting account ketianzhang1-lang (proof implementation, with OpenAI ChatGPT assistance).
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-!
# JSP-000736 / Erdős 885: Bremner's k = 4 case

Known mathematics: Andrew Bremner (2019), DOI 10.1142/S1793042119500581.
The concrete witness was located in Patrick White's July 27, 2026 report:
https://erdosproblemaday.com/day/885-factor-difference-k5
The definition and main theorem statement match Formal Conjectures, Erdős 885.
No result about all k or the open k = 5 case is claimed.
-/
namespace JSP000736

/-- The original complementary-factor difference set. -/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

/-- Bremner's four positive integers. -/
def numbers : Finset ℕ := {26128575, 291722431, 561117375, 713526975}

/-- Four common complementary-factor differences. -/
def differences : Finset ℕ := {126, 16110, 33390, 75390}

/-- Finiteness is needed: `Set.ncard` is zero for an infinite set. -/
theorem factorDifferenceSet_finite (n : ℕ) (hn : 0 < n) :
    (factorDifferenceSet n).Finite := by
  apply (Set.finite_Icc 0 n).subset
  rintro d ⟨a, b, hab, hd⟩
  have ha : a ≤ n := Nat.le_of_dvd hn ⟨b, hab⟩
  have hb : b ≤ n := Nat.le_of_dvd hn ⟨a, by simpa [Nat.mul_comm] using hab⟩
  have hbound : |(a : ℤ) - b| ≤ (n : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  exact ⟨Nat.zero_le d, by omega⟩

/-- Sixteen explicit factor-pair certificates, checked by the Lean kernel. -/
theorem common_differences :
    (↑differences : Set ℕ) ⊆ ⋂ n ∈ numbers, factorDifferenceSet n := by
  intro d hd
  simp only [Set.mem_iInter]
  intro n hn
  simp only [numbers, Finset.mem_insert, Finset.mem_singleton] at hn
  simp only [differences, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hn with rfl | rfl | rfl | rfl
  · rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨5049, 5175, by norm_num, by norm_num⟩
    · exact ⟨1485, 17595, by norm_num, by norm_num⟩
    · exact ⟨765, 34155, by norm_num, by norm_num⟩
    · exact ⟨345, 75735, by norm_num, by norm_num⟩
  · rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨17017, 17143, by norm_num, by norm_num⟩
    · exact ⟨10829, 26939, by norm_num, by norm_num⟩
    · exact ⟨7189, 40579, by norm_num, by norm_num⟩
    · exact ⟨3689, 79079, by norm_num, by norm_num⟩
  · rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨23625, 23751, by norm_num, by norm_num⟩
    · exact ⟨16965, 33075, by norm_num, by norm_num⟩
    · exact ⟨12285, 45675, by norm_num, by norm_num⟩
    · exact ⟨6825, 82215, by norm_num, by norm_num⟩
  · rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨26649, 26775, by norm_num, by norm_num⟩
    · exact ⟨19845, 35955, by norm_num, by norm_num⟩
    · exact ⟨14805, 48195, by norm_num, by norm_num⟩
    · exact ⟨8505, 83895, by norm_num, by norm_num⟩

/-- Exactly the k = 4 target statement from Formal Conjectures. -/
theorem erdos_885_k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨numbers, ?_, by decide, ?_⟩
  · intro n hn
    simp only [numbers, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  · have hf : (⋂ n ∈ numbers, factorDifferenceSet n).Finite :=
      (factorDifferenceSet_finite 26128575 (by norm_num)).subset
        (Set.iInter_subset_of_subset 26128575
          (Set.iInter_subset_of_subset (by decide : 26128575 ∈ numbers) Set.Subset.rfl))
    have hcard := Set.ncard_le_ncard common_differences hf
    simpa only [Set.ncard_coe_finset, show differences.card = 4 from by decide] using hcard

end JSP000736
