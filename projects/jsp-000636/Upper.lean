import Lower
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Sqrt

/-!
A pair-label variant of the He--Tang construction for Erdős 776.
It gives an explicit, weaker upper threshold with a square-root error.
This is a formalization supplement, not a claim of a new mathematical bound.
-/

namespace JSP000636
open Finset

theorem choose_ge_self {q s : ℕ} (hs : 0 < s) (hsq : s < q) :
    q ≤ q.choose s := by
  induction q generalizing s with
  | zero => omega
  | succ q ih =>
    by_cases h1 : s = 1
    · simp [h1]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    rw [Nat.choose_succ_succ]
    have hqt : q ≤ q.choose t := ih (by omega) (by omega)
    have hp : 0 < q.choose t.succ := Nat.choose_pos (by omega)
    omega

theorem pair_capacity (m : ℕ) (hm : 4 ≤ m) : 2*m-3 ≤ m.choose 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [show 2 = 1+1 by rfl, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    change 2*(m+1)-3 ≤ m + m.choose 2
    omega

theorem select_subsets {α : Type*} [DecidableEq α]
    (S : Finset α) (r s : ℕ) (h : r ≤ S.card.choose s) :
    ∃ f : Fin r → Finset α, Function.Injective f ∧
      ∀ i, f i ⊆ S ∧ (f i).card = s := by
  classical
  have hc : Fintype.card (Fin r) ≤ Fintype.card (↥(S.powersetCard s)) := by
    simpa only [Fintype.card_fin, Fintype.card_coe, card_powersetCard] using h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact mem_powersetCard.mp (e i).property

structure HalfFamily (n r k : ℕ) where
  a : Fin n
  f : Fin (k-1) → Fin r → Finset (Fin n)
  card_f : ∀ t j, (f t j).card = t.val+2
  inj_f : ∀ t, Function.Injective (f t)
  common : ∀ t j, a ∈ f t j
  anti : ∀ t j s i, f t j ⊆ f s i → f t j = f s i

namespace HalfFamily
variable {n r k : ℕ} (H : HalfFamily n r k)

def family : Finset (Finset (Fin n)) :=
  univ.image (fun p : Fin (k-1) × Fin r => H.f p.1 p.2)

theorem mem_family (A : Finset (Fin n)) :
    A ∈ H.family ↔ ∃ t j, H.f t j = A := by
  simp [family]

theorem antichain : Antichain H.family := by
  intro A hA B hB hsub
  obtain ⟨t,j,rfl⟩ := (H.mem_family A).mp hA
  obtain ⟨s,i,rfl⟩ := (H.mem_family B).mp hB
  exact H.anti t j s i hsub

theorem card_le {A : Finset (Fin n)} (hA : A ∈ H.family) : A.card ≤ k := by
  obtain ⟨t,j,rfl⟩ := (H.mem_family A).mp hA
  rw [H.card_f]
  have := t.isLt
  omega

theorem common_mem {A : Finset (Fin n)} (hA : A ∈ H.family) : H.a ∈ A := by
  obtain ⟨t,j,rfl⟩ := (H.mem_family A).mp hA
  exact H.common t j

theorem multiplicity : Multiplicity r H.family := by
  intro A hA
  obtain ⟨t,j,rfl⟩ := (H.mem_family A).mp hA
  have hsub : univ.image (H.f t) ⊆ H.family.filter (fun B => B.card = (H.f t j).card) := by
    intro B hB
    obtain ⟨i,_,rfl⟩ := mem_image.mp hB
    exact mem_filter.mpr ⟨(H.mem_family _).mpr ⟨t,i,rfl⟩, by rw [H.card_f,H.card_f]⟩
  have hc : (univ.image (H.f t)).card = r := by
    rw [card_image_of_injective _ (H.inj_f t)]
    simp
  simpa only [hc] using card_le_card hsub

def full : Finset (Finset (Fin n)) := H.family ∪ complements H.family

theorem full_antichain (hn : 2*k ≤ n) : Antichain H.full := by
  intro A hA B hB hsub
  rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
  · exact H.antichain A hA B hB hsub
  · obtain ⟨C,hC,rfl⟩ := mem_image.mp hB
    exact False.elim ((mem_compl.mp (hsub (H.common_mem hA))) (H.common_mem hC))
  · obtain ⟨C,hC,rfl⟩ := mem_image.mp hA
    apply eq_of_subset_of_card_le hsub
    have hc := H.card_le hC
    have hb := H.card_le hB
    simp only [card_compl,Fintype.card_fin]
    omega
  · exact antichain_complements H.antichain A hA B hB hsub

theorem full_multiplicity : Multiplicity r H.full := by
  intro A hA
  rcases mem_union.mp hA with hA | hA
  · exact (H.multiplicity A hA).trans (card_le_card (filter_subset_filter _ subset_union_left))
  · exact (multiplicity_complements H.multiplicity A hA).trans
      (card_le_card (filter_subset_filter _ subset_union_right))

theorem all_sizes (hr : 0 < r) (hk : 2 ≤ k) (hn : n ≤ 2*k+1) :
    Icc 2 (n-2) ⊆ sizes H.full := by
  intro t ht
  obtain ⟨ht2,htn⟩ := mem_Icc.mp ht
  let j : Fin r := ⟨0,hr⟩
  by_cases htk : t ≤ k
  · let s : Fin (k-1) := ⟨t-2,by omega⟩
    apply mem_image.mpr
    refine ⟨H.f s j,mem_union_left _ ((H.mem_family _).mpr ⟨s,j,rfl⟩),?_⟩
    rw [H.card_f]
    dsimp [s]
    omega
  · have hlow : 2 ≤ n-t := by omega
    have hhigh : n-t ≤ k := by omega
    let s : Fin (k-1) := ⟨n-t-2,by omega⟩
    apply mem_image.mpr
    refine ⟨(H.f s j)ᶜ,mem_union_right _ (mem_image.mpr
      ⟨H.f s j,(H.mem_family _).mpr ⟨s,j,rfl⟩,rfl⟩),?_⟩
    rw [card_compl,Fintype.card_fin,H.card_f]
    dsimp [s]
    omega

theorem full_size_count (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hnlo : 2*k ≤ n) (hnhi : n ≤ 2*k+1) :
    (sizes H.full).card = n-3 := by
  apply Nat.le_antisymm
  · exact size_count_le n r (by omega) hr H.full (H.full_antichain hnlo) H.full_multiplicity
  · have hh := card_le_card (H.all_sizes (by omega) hk hnhi)
    simpa using hh

end HalfFamily

end JSP000636
