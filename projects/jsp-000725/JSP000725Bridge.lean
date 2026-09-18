import JSP000725
import ErdosProblems.Erdos874.Foundations

/-! Our statement bridge preserves the original natural-number predicate,
including empty subsets, and identifies its extremal function with the
attributed integer restricted-sumset development. -/

namespace JSP000725
open Finset

def natIntEmbedding : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
def toInt (A : Finset ℕ) : Finset ℤ := A.map natIntEmbedding

@[simp] theorem card_toInt (A : Finset ℕ) : (toInt A).card = A.card := by
  simp [toInt]

@[simp] theorem sum_toInt (A : Finset ℕ) :
    (∑ x ∈ toInt A, x) = ((∑ x ∈ A, x : ℕ) : ℤ) := by
  simp [toInt, natIntEmbedding, Nat.cast_sum]

theorem admissible_iff_cardinality_determined (A : Finset ℕ) :
    Admissible A ↔ Erdos874.HasCardinalityDeterminedSums (toInt A) := by
  constructor
  · intro h S hS T hT hsum
    obtain ⟨U, hU, rfl⟩ := Finset.subset_map_iff.mp hS
    obtain ⟨V, hV, rfl⟩ := Finset.subset_map_iff.mp hT
    have he : (∑ x ∈ U, x) = (∑ x ∈ V, x) := by
      have : ((∑ x ∈ U, x : ℕ) : ℤ) = ((∑ x ∈ V, x : ℕ) : ℤ) := by
        change (∑ x ∈ toInt U, x) = (∑ x ∈ toInt V, x) at hsum
        simpa only [sum_toInt] using hsum
      exact_mod_cast this
    simpa using h U hU V hV he
  · intro h S hS T hT hsum
    have hS' : toInt S ⊆ toInt A := Finset.map_subset_map.mpr hS
    have hT' : toInt T ⊆ toInt A := Finset.map_subset_map.mpr hT
    have he : (∑ x ∈ toInt S, x) = (∑ x ∈ toInt T, x) := by
      simp only [sum_toInt, hsum]
    simpa using h (toInt S) hS' (toInt T) hT' he

theorem admissible_iff_upstream {A : Finset ℕ} (hpos : ∀ x ∈ A, 0 < x) :
    Admissible A ↔ Erdos874.IsAdmissible (toInt A) := by
  rw [Erdos874.isAdmissible_iff_card_eq_of_sum_eq]
  · exact admissible_iff_cardinality_determined A
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    change (0 : ℤ) < (a : ℤ)
    exact_mod_cast hpos a ha

theorem bounded_iff {N : ℕ} {A : Finset ℕ} :
    toInt A ⊆ Erdos874.ambient N ↔ A ⊆ Icc 1 N := by
  constructor
  · intro h a ha
    have hx : (a : ℤ) ∈ toInt A := Finset.mem_map.mpr ⟨a, ha, rfl⟩
    have := Erdos874.mem_ambient.mp (h hx)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    have := mem_Icc.mp (h ha)
    apply Erdos874.mem_ambient.mpr
    change 1 ≤ (a : ℤ) ∧ (a : ℤ) ≤ (N : ℤ)
    constructor <;> omega

theorem boundedAdmissible_iff {N : ℕ} {A : Finset ℕ} :
    Erdos874.IsBoundedAdmissible N (toInt A) ↔ A ⊆ Icc 1 N ∧ Admissible A := by
  rw [Erdos874.IsBoundedAdmissible, bounded_iff]
  constructor
  · rintro ⟨hA, h⟩
    exact ⟨hA, (admissible_iff_upstream (fun x hx => by
      have := (mem_Icc.mp (hA hx)).1; omega)).mpr h⟩
  · rintro ⟨hA, h⟩
    exact ⟨hA, (admissible_iff_upstream (fun x hx => by
      have := (mem_Icc.mp (hA hx)).1; omega)).mp h⟩

theorem exists_nat_preimage {N : ℕ} {B : Finset ℤ}
    (hB : B ⊆ Erdos874.ambient N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ toInt A = B := by
  let A := B.image Int.toNat
  have he : toInt A = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hpos := (Erdos874.mem_ambient.mp (hB hb)).1
      change (b.toNat : ℤ) ∈ B
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ b)] using hb
    · intro hx
      have hpos := (Erdos874.mem_ambient.mp (hB hx)).1
      refine Finset.mem_map.mpr ⟨x.toNat, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      exact Int.toNat_of_nonneg (by omega)
  exact ⟨A, bounded_iff.mp (he ▸ hB), he⟩

noncomputable def admissibleFamily (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Icc 1 N).powerset.filter Admissible

@[simp] theorem mem_admissibleFamily {N : ℕ} {A : Finset ℕ} :
    A ∈ admissibleFamily N ↔ A ⊆ Icc 1 N ∧ Admissible A := by
  classical
  simp [admissibleFamily]

noncomputable def maxCard (N : ℕ) : ℕ := (admissibleFamily N).sup Finset.card

theorem maxCard_eq_upstream (N : ℕ) : maxCard N = Erdos874.k N := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    have hb := boundedAdmissible_iff.mpr (mem_admissibleFamily.mp hA)
    simpa using Erdos874.card_le_k hb
  · obtain ⟨B, hB, hc⟩ := Erdos874.exists_boundedAdmissible_card_eq_k N
    obtain ⟨A, hA, he⟩ := exists_nat_preimage hB.1
    have hba : Erdos874.IsBoundedAdmissible N (toInt A) := he ▸ hB
    have ha := mem_admissibleFamily.mpr (boundedAdmissible_iff.mp hba)
    have hcard : A.card = Erdos874.k N := by simpa only [← he, card_toInt] using hc
    rw [← hcard]
    exact Finset.le_sup ha

end JSP000725
