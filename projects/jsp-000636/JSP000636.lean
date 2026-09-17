import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
The universal obstruction for the Erdős–Trotter multiplicity problem,
JSP-000636 / Erdős 776. This proves Lemma 2.5 of He and Tang,
arXiv:2602.09803v1, for every n >= 4 and every r >= 2.
It does not determine the threshold n₀(r).
The proof was written with OpenAI ChatGPT assistance.
-/

namespace JSP000636
open Finset

variable {n : ℕ}

/-- Inclusion between members of the family forces equality. -/
def Antichain (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- Each occurring size has at least r distinct members. -/
def Multiplicity (r : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, r ≤ (F.filter (fun B => B.card = A.card)).card

def sizes (F : Finset (Finset (Fin n))) : Finset ℕ := F.image Finset.card

def Twins (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∃ B ∈ F, B.card = A.card ∧ B ≠ A

def complements (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  F.image (fun A => Aᶜ)

theorem antichain_iff_isAntichain (F : Finset (Finset (Fin n))) :
    Antichain F ↔ IsAntichain (· ⊆ ·) (↑F : Set (Finset (Fin n))) := by
  constructor
  · intro h A hA B hB hne hsub
    exact hne (h A hA B hB hsub)
  · intro h A hA B hB hsub
    by_contra hne
    exact h hA hB hne hsub

theorem twins_of_multiplicity {r : ℕ} {F : Finset (Finset (Fin n))}
    (hr : 2 ≤ r) (h : Multiplicity r F) : Twins F := by
  intro A hA
  obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp
    (show 1 < (F.filter (fun B => B.card = A.card)).card from
      lt_of_lt_of_le (by omega) (h A hA))
  simp only [Finset.mem_filter] at hB hC
  by_cases hBA : B = A
  · exact ⟨C, hC.1, hC.2, by simpa [hBA] using hBC.symm⟩
  · exact ⟨B, hB.1, hB.2, hBA⟩

theorem card_pos_of_twins {F : Finset (Finset (Fin n))} (h : Twins F)
    {A : Finset (Fin n)} (hA : A ∈ F) : 0 < A.card := by
  obtain ⟨B, _, hB, hne⟩ := h A hA
  by_contra! hz
  have hAz : A = ∅ := Finset.card_eq_zero.mp (by omega)
  have hBz : B = ∅ := Finset.card_eq_zero.mp (by omega)
  exact hne (hBz.trans hAz.symm)

theorem antichain_complements {F : Finset (Finset (Fin n))}
    (h : Antichain F) : Antichain (complements F) := by
  intro A hA B hB hAB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB
  have hDC : D ⊆ C := by simpa using Finset.compl_subset_compl.mp hAB
  exact congrArg (fun S : Finset (Fin n) => Sᶜ) (h D hD C hC hDC).symm

theorem twins_complements {F : Finset (Finset (Fin n))}
    (h : Twins F) : Twins (complements F) := by
  intro A hA
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨D, hD, hcard, hne⟩ := h C hC
  refine ⟨Dᶜ, Finset.mem_image.mpr ⟨D, hD, rfl⟩, ?_, ?_⟩
  · simp only [Finset.card_compl, hcard]
  · intro heq
    exact hne (by simpa using congrArg (fun S : Finset (Fin n) => Sᶜ) heq)

theorem card_sizes_complements (F : Finset (Finset (Fin n))) :
    (sizes (complements F)).card = (sizes F).card := by
  have heq : sizes (complements F) = (sizes F).image (fun t => n - t) := by
    simp only [sizes, complements, Finset.image_image, Function.comp_def,
      Finset.card_compl, Fintype.card_fin]
  rw [heq]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hb
  have hA : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hB : B.card ≤ n := by simpa using Finset.card_le_univ B
  dsimp only at hab
  omega

/-- Two singleton members leave at most n-3 elements available to every
occurring size: the top possible residual set would be unique. -/
theorem card_le_of_singleton (hn : 4 ≤ n) {F : Finset (Finset (Fin n))}
    (ha : Antichain F) (ht : Twins F) (h1 : 1 ∈ sizes F)
    {A : Finset (Fin n)} (hA : A ∈ F) : A.card ≤ n - 3 := by
  obtain ⟨X, hX, hXcard⟩ := Finset.mem_image.mp h1
  obtain ⟨Y, hY, hYcard, hYX⟩ := ht X hX
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hXcard
  have hycard : Y.card = 1 := by simpa using hYcard
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hycard
  have hxy : x ≠ y := by
    intro heq
    exact hYX (by simp [heq])
  let U : Finset (Fin n) := (Finset.univ.erase x).erase y
  have hU : U.card = n - 2 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (by simp [hxy.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ x)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hsub : ∀ C ∈ F, 1 < C.card → C ⊆ U := by
    intro C hC hc z hz
    have hxC : x ∉ C := by
      intro hxc
      have heq := ha {x} hX C hC (Finset.singleton_subset_iff.mpr hxc)
      have := congrArg Finset.card heq
      simp only [Finset.card_singleton] at this
      omega
    have hyC : y ∉ C := by
      intro hyc
      have heq := ha {y} hY C hC (Finset.singleton_subset_iff.mpr hyc)
      have := congrArg Finset.card heq
      simp only [Finset.card_singleton] at this
      omega
    simp only [U, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hyC (h ▸ hz), fun h => hxC (h ▸ hz)⟩
  by_cases hsmall : A.card ≤ 1
  · omega
  obtain ⟨B, hB, hBA, hne⟩ := ht A hA
  have hAU := hsub A hA (by omega)
  have hBU := hsub B hB (by omega)
  have hAle := Finset.card_le_card hAU
  have hlt : A.card < U.card := by
    by_contra! hh
    have hAUeq := Finset.eq_of_subset_of_card_le hAU hh
    have hBUeq := Finset.eq_of_subset_of_card_le hBU (by omega)
    exact hne (hBUeq.trans hAUeq.symm)
  omega

theorem size_count_le_of_singleton (hn : 4 ≤ n) {F : Finset (Finset (Fin n))}
    (ha : Antichain F) (ht : Twins F) (h1 : 1 ∈ sizes F) :
    (sizes F).card ≤ n - 3 := by
  have hsub : sizes F ⊆ Finset.Icc 1 (n - 3) := by
    intro t htmem
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp htmem
    exact Finset.mem_Icc.mpr ⟨card_pos_of_twins ht hA,
      card_le_of_singleton hn ha ht h1 hA⟩
  have := Finset.card_le_card hsub
  simpa using this

/-- He–Tang Lemma 2.5: all n >= 4 and r >= 2, with distinct sets and
ordinary (non-strict) inclusion. -/
theorem size_count_le (n r : ℕ) (hn : 4 ≤ n) (hr : 2 ≤ r)
    (F : Finset (Finset (Fin n))) (ha : Antichain F) (hm : Multiplicity r F) :
    (sizes F).card ≤ n - 3 := by
  have ht := twins_of_multiplicity hr hm
  by_cases h1 : 1 ∈ sizes F
  · exact size_count_le_of_singleton hn ha ht h1
  by_cases hc1 : 1 ∈ sizes (complements F)
  · rw [← card_sizes_complements F]
    exact size_count_le_of_singleton hn (antichain_complements ha)
      (twins_complements ht) hc1
  have hsub : sizes F ⊆ Finset.Icc 2 (n - 2) := by
    intro t htmem
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp htmem
    have hpos := card_pos_of_twins ht hA
    have hne : A.card ≠ 1 := by
      intro heq
      exact h1 (Finset.mem_image.mpr ⟨A, hA, heq⟩)
    have hAc : Aᶜ ∈ complements F := Finset.mem_image.mpr ⟨A, hA, rfl⟩
    have hcpos := card_pos_of_twins (twins_complements ht) hAc
    have hcne : Aᶜ.card ≠ 1 := by
      intro heq
      exact hc1 (Finset.mem_image.mpr ⟨Aᶜ, hAc, heq⟩)
    simp only [Finset.card_compl, Fintype.card_fin] at hcpos hcne
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hh := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hh
  omega

/-- Original exact-multiplicity convention. -/
def ExactMultiplicity (r : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r

theorem card_eq_mul_size_count {r : ℕ} {F : Finset (Finset (Fin n))}
    (hm : ExactMultiplicity r F) : F.card = r * (sizes F).card := by
  rw [Finset.card_eq_sum_card_image Finset.card F]
  calc
    ∑ t ∈ F.image Finset.card, (F.filter (fun A => A.card = t)).card =
        ∑ _t ∈ F.image Finset.card, r := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ht
      exact hm A hA
    _ = r * (sizes F).card := by simp [sizes, Nat.mul_comm]

/-- In the original wording, at most r(n-3) sets are possible. -/
theorem exact_multiplicity_card_le (n r : ℕ) (hn : 4 ≤ n) (hr : 2 ≤ r)
    (F : Finset (Finset (Fin n)))
    (ha : IsAntichain (· ⊆ ·) (↑F : Set (Finset (Fin n))))
    (hm : ExactMultiplicity r F) : F.card ≤ r * (n - 3) := by
  rw [card_eq_mul_size_count hm]
  apply Nat.mul_le_mul_left
  exact size_count_le n r hn hr F ((antichain_iff_isAntichain F).mpr ha)
    (fun A hA => (hm A hA).ge)

/-- The bound is attained at its smallest permitted n. -/
theorem sharp_at_four :
    ∃ F : Finset (Finset (Fin 4)), Antichain F ∧ ExactMultiplicity 2 F ∧
      (sizes F).card = 4 - 3 ∧ F.card = 2 * (4 - 3) := by
  refine ⟨{{0, 1}, {0, 2}}, ?_⟩
  unfold Antichain ExactMultiplicity sizes
  decide

/-- The restriction n >= 4 cannot simply be dropped. -/
theorem three_is_exception :
    ∃ F : Finset (Finset (Fin 3)), Antichain F ∧ ExactMultiplicity 2 F ∧
      3 - 3 < (sizes F).card := by
  refine ⟨{{0}, {1}}, ?_⟩
  unfold Antichain ExactMultiplicity sizes
  decide

/-- Multiplicity one does not satisfy the same upper bound. -/
theorem one_is_exception :
    ∃ F : Finset (Finset (Fin 4)), Antichain F ∧ ExactMultiplicity 1 F ∧
      4 - 3 < (sizes F).card := by
  refine ⟨{{0}, {1, 2}}, ?_⟩
  unfold Antichain ExactMultiplicity sizes
  decide

end JSP000636
