import JSP000636
import Mathlib.Data.Finset.Prod

/-!
The threshold lower bound in He and Tang, arXiv:2602.09803v1, Theorem 1.4.
The proof uses their common-star reduction and a symmetric middle-level argument.
-/

namespace JSP000636
open Finset

section Pairs
variable {α : Type*} [DecidableEq α]

theorem pair_eq_of_mem {A : Finset α} {x y : α}
    (hA : A.card = 2) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) : A = {x,y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hx,hy⟩
  · simp [hA, hxy]

theorem pair_of_mem {A : Finset α} {x : α} (hA : A.card = 2) (hx : x ∈ A) :
    ∃ y, y ≠ x ∧ A = {x,y} := by
  have he : (A.erase x).card = 1 := by rw [Finset.card_erase_of_mem hx, hA]
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp he
  have hym : y ∈ A.erase x := by rw [hy]; simp
  refine ⟨y, (Finset.mem_erase.mp hym).1, ?_⟩
  exact pair_eq_of_mem hA hx (Finset.mem_erase.mp hym).2
    (Finset.mem_erase.mp hym).1.symm

def crossPairs (A B : Finset α) : Finset (Finset α) :=
  (A.product B).image (fun p => {p.1,p.2})

theorem mem_crossPairs {A B C : Finset α} (hC : C.card = 2)
    (hAB : Disjoint A B) (hCA : ¬ Disjoint C A) (hCB : ¬ Disjoint C B) :
    C ∈ crossPairs A B := by
  obtain ⟨a,haC,haA⟩ := Finset.not_disjoint_iff.mp hCA
  obtain ⟨b,hbC,hbB⟩ := Finset.not_disjoint_iff.mp hCB
  have hab : a ≠ b := by
    intro h
    exact (Finset.disjoint_left.mp hAB haA) (h ▸ hbB)
  exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨haA,hbB⟩,
    (pair_eq_of_mem hC haC hbC hab).symm⟩

theorem hits_crossPairs {A B C : Finset α} (hA : A.card = 2)
    (hB : B.card = 2) (hC : C.card = 2)
    (h : ∀ D ∈ crossPairs A B, ¬ Disjoint C D) : C = A ∨ C = B := by
  by_cases hAC : A ⊆ C
  · exact Or.inl (Finset.eq_of_subset_of_card_le hAC (by omega)).symm
  obtain ⟨a,ha,haC⟩ := Finset.not_subset.mp hAC
  have hBC : B ⊆ C := by
    intro b hb
    by_contra hbC
    have hp : ({a,b} : Finset α) ∈ crossPairs A B :=
      Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩
    apply h {a,b} hp
    simp [Finset.disjoint_right, haC, hbC]
  exact Or.inr (Finset.eq_of_subset_of_card_le hBC (by omega)).symm

theorem cross_intersecting_pairs_intersect {E M : Finset (Finset α)}
    (hE : ∀ A ∈ E, A.card = 2) (hM : ∀ B ∈ M, B.card = 2)
    (hcE : 4 ≤ E.card) (hcM : 4 ≤ M.card)
    (hc : ∀ A ∈ E, ∀ B ∈ M, ¬ Disjoint A B) :
    ∀ A ∈ E, ∀ B ∈ E, ¬ Disjoint A B := by
  intro A hA B hB hdis
  have hsub : M ⊆ crossPairs A B := by
    intro C hC
    exact mem_crossPairs (hM C hC) hdis
      (fun hh => hc A hA C hC hh.symm) (fun hh => hc B hB C hC hh.symm)
  have hsize : (crossPairs A B).card ≤ 4 := by
    calc
      _ ≤ (A.product B).card := Finset.card_image_le
      _ = A.card * B.card := Finset.card_product A B
      _ = 4 := by rw [hE A hA,hE B hB]
  have heq : M = crossPairs A B := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hEsub : E ⊆ {A,B} := by
    intro C hC
    have hh := hits_crossPairs (hE A hA) (hE B hB) (hE C hC)
      (fun D hD => hc C hC D (heq ▸ hD))
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hh := Finset.card_le_card hEsub
  have hbnd : ({A,B} : Finset (Finset α)).card ≤ 2 := Finset.card_le_two
  omega

theorem intersecting_pairs_star {E : Finset (Finset α)}
    (hE : ∀ A ∈ E, A.card = 2) (hcE : 4 ≤ E.card)
    (hi : ∀ A ∈ E, ∀ B ∈ E, ¬ Disjoint A B) :
    ∃ x, ∀ A ∈ E, x ∈ A := by
  classical
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < A.card by rw [hE A hA]; omega)
  obtain ⟨b,hba,rfl⟩ := pair_of_mem (hE A hA) ha
  by_cases hall : ∀ C ∈ E, a ∈ C
  · exact ⟨a,hall⟩
  push Not at hall
  obtain ⟨B,hB,haB⟩ := hall
  have hbB : b ∈ B := by
    have hh := hi {a,b} hA B hB
    simpa [Finset.disjoint_left, haB] using hh
  obtain ⟨c,hcb,rfl⟩ := pair_of_mem (hE B hB) hbB
  have hac : a ≠ c := by simpa [hba.symm] using haB
  by_cases hallb : ∀ C ∈ E, b ∈ C
  · exact ⟨b,hallb⟩
  push Not at hallb
  obtain ⟨C,hC,hbC⟩ := hallb
  have haC : a ∈ C := by
    have hh := hi {a,b} hA C hC
    simpa [Finset.disjoint_left, hbC] using hh
  have hcC : c ∈ C := by
    have hh := hi {b,c} hB C hC
    simpa [Finset.disjoint_left, hbC] using hh
  have hCeq := pair_eq_of_mem (hE C hC) haC hcC hac
  subst C
  have hsub : E ⊆ {{a,b},{b,c},{a,c}} := by
    intro D hD
    by_cases haD : a ∈ D
    · by_cases hbD : b ∈ D
      · have := pair_eq_of_mem (hE D hD) haD hbD hba.symm
        simp [this]
      · have hcD : c ∈ D := by
          have hh := hi {b,c} hB D hD
          simpa [Finset.disjoint_left,hbD] using hh
        have := pair_eq_of_mem (hE D hD) haD hcD hac
        simp [this]
    · have hbD : b ∈ D := by
        have hh := hi {a,b} hA D hD
        simpa [Finset.disjoint_left,haD] using hh
      have hcD : c ∈ D := by
        have hh := hi {a,c} hC D hD
        simpa [Finset.disjoint_left,haD] using hh
      have := pair_eq_of_mem (hE D hD) hbD hcD hcb.symm
      simp [this]
  have hcard := Finset.card_le_card hsub
  have hbound : ({{a,b},{b,c},{a,c}} : Finset (Finset α)).card ≤ 3 := by
    calc
      _ ≤ ({{b,c},{a,c}} : Finset (Finset α)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 3 := by have := (Finset.card_le_two : ({{b,c},{a,c}} : Finset (Finset α)).card ≤ 2); omega
  omega

end Pairs

variable {n : ℕ}

def level (F : Finset (Finset (Fin n))) (k : ℕ) : Finset (Finset (Fin n)) :=
  F.filter (fun A => A.card = k)

def leaves (E : Finset (Finset (Fin n))) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun y => y ≠ x ∧ ({x,y} : Finset (Fin n)) ∈ E)

theorem star_image {E : Finset (Finset (Fin n))} {x : Fin n}
    (hE : ∀ A ∈ E, A.card = 2) (hx : ∀ A ∈ E, x ∈ A) :
    E = (leaves E x).image (fun y => {x,y}) := by
  ext A
  constructor
  · intro hA
    obtain ⟨y,hy,rfl⟩ := pair_of_mem (hE A hA) (hx A hA)
    exact Finset.mem_image.mpr ⟨y,by simp [leaves,hy,hA],rfl⟩
  · intro hA
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_filter.mp hy).2.2

theorem card_leaves {E : Finset (Finset (Fin n))} {x : Fin n}
    (hE : ∀ A ∈ E, A.card = 2) (hx : ∀ A ∈ E, x ∈ A) :
    (leaves E x).card = E.card := by
  conv_rhs => rw [star_image hE hx]
  symm
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  change ({x,a} : Finset (Fin n)) = {x,b} at heq
  have hax := (Finset.mem_filter.mp ha).2.1
  have ham : a ∈ ({x,b} : Finset (Fin n)) := heq ▸ (by simp : a ∈ ({x,a} : Finset (Fin n)))
  simpa [hax] using ham

theorem common_star {E M : Finset (Finset (Fin n))}
    (hE : ∀ A ∈ E, A.card = 2) (hM : ∀ B ∈ M, B.card = 2)
    (hcE : 4 ≤ E.card) (hcM : 4 ≤ M.card)
    (hc : ∀ A ∈ E, ∀ B ∈ M, ¬ Disjoint A B) :
    ∃ x, (∀ A ∈ E, x ∈ A) ∧ (∀ B ∈ M, x ∈ B) := by
  obtain ⟨x,hx⟩ := intersecting_pairs_star hE hcE
    (cross_intersecting_pairs_intersect hE hM hcE hcM hc)
  refine ⟨x,hx,?_⟩
  intro B hB
  by_contra hxB
  have hsub : leaves E x ⊆ B := by
    intro y hy
    have he := (Finset.mem_filter.mp hy).2.2
    have hh := hc {x,y} he B hB
    simpa [Finset.disjoint_left,hxB] using hh
  have hh := Finset.card_le_card hsub
  rw [card_leaves hE hx,hM B hB] at hh
  omega

theorem level_card_ge {r k : ℕ} {F : Finset (Finset (Fin n))}
    (hm : Multiplicity r F) (hk : k ∈ sizes F) : r ≤ (level F k).card := by
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hk
  exact hm A hA

theorem complements_involutive (F : Finset (Finset (Fin n))) :
    complements (complements F) = F := by
  simp [complements,Finset.image_image]

theorem multiplicity_complements {r : ℕ} {F : Finset (Finset (Fin n))}
    (hm : Multiplicity r F) : Multiplicity r (complements F) := by
  intro A hA
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hA
  let S := level F C.card
  have hcard : (complements S).card = S.card := by
    apply Finset.card_image_iff.mpr
    intro B hB D hD heq
    simpa using congrArg (fun X : Finset (Fin n) => Xᶜ) heq
  have hsub : complements S ⊆ level (complements F) Cᶜ.card := by
    intro B hB
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hDF,hDc⟩ := Finset.mem_filter.mp hD
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨D,hDF,rfl⟩,by simp [Finset.card_compl,hDc]⟩
  exact (hm C hC).trans (hcard ▸ Finset.card_le_card hsub)

def singles (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ({x} : Finset (Fin n)) ∈ F)

theorem card_singles (F : Finset (Finset (Fin n))) :
    (singles F).card = (level F 1).card := by
  have heq : level F 1 = (singles F).image (fun x => {x}) := by
    ext A
    simp only [level,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨hA,hc⟩
      obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hc
      exact ⟨x,by simpa [singles] using hA,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨by simpa [singles] using hx,by simp⟩
  rw [heq,Finset.card_image_iff.mpr]
  intro a ha b hb heq
  simpa using heq

theorem sizes_bound_of_singles {r : ℕ} (hn : r+1 ≤ n)
    {F : Finset (Finset (Fin n))} (ha : Antichain F) (hm : Multiplicity r F)
    (hr : 2 ≤ r) (h1 : 1 ∈ sizes F) : (sizes F).card ≤ n-r := by
  have hs : r ≤ (singles F).card := by rw [card_singles]; exact level_card_ge hm h1
  have hb : ∀ A ∈ F, A.card ≤ n-r := by
    intro A hA
    by_cases hc : A.card ≤ 1
    · omega
    have hsub : A ⊆ (singles F)ᶜ := by
      intro x hx
      simp only [Finset.mem_compl, singles,Finset.mem_filter,Finset.mem_univ,true_and]
      intro hsingle
      have heq := ha {x} hsingle A hA (Finset.singleton_subset_iff.mpr hx)
      have := congrArg Finset.card heq
      simp only [Finset.card_singleton] at this
      omega
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_compl,Fintype.card_fin] at hh
    omega
  have hsub : sizes F ⊆ Finset.Icc 1 (n-r) := by
    intro k hk
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨card_pos_of_twins (twins_of_multiplicity hr hm) hA,hb A hA⟩
  simpa using Finset.card_le_card hsub

theorem full_profile {r : ℕ} (hn : r+3 ≤ n) (hr : 4 ≤ r)
    {F : Finset (Finset (Fin n))} (ha : Antichain F) (hm : Multiplicity r F)
    (hs : (sizes F).card = n-3) : sizes F = Finset.Icc 2 (n-2) := by
  have h1 : 1 ∉ sizes F := by
    intro h
    have hh := sizes_bound_of_singles (by omega : r+1 ≤ n) ha hm (by omega) h
    omega
  have hc1 : 1 ∉ sizes (complements F) := by
    intro h
    have hh := sizes_bound_of_singles (by omega : r+1 ≤ n) (antichain_complements ha)
      (multiplicity_complements hm) (by omega) h
    rw [card_sizes_complements] at hh
    omega
  have ht := twins_of_multiplicity (by omega : 2 ≤ r) hm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hk
    have hpos := card_pos_of_twins ht hA
    have hAc : Aᶜ ∈ complements F := Finset.mem_image.mpr ⟨A,hA,rfl⟩
    have hcpos := card_pos_of_twins (twins_complements ht) hAc
    have hne : A.card ≠ 1 := fun h => h1 (Finset.mem_image.mpr ⟨A,hA,h⟩)
    have hcne : Aᶜ.card ≠ 1 := fun h => hc1 (Finset.mem_image.mpr ⟨Aᶜ,hAc,h⟩)
    simp only [Finset.card_compl,Fintype.card_fin] at hcpos hcne
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · simp only [Nat.card_Icc]
    omega

theorem small_contains_center {F : Finset (Finset (Fin n))}
    (ha : Antichain F) {A : Finset (Fin n)} (hA : A ∈ F) (x : Fin n)
    (hsmall : A.card < n-2)
    (hcount : A.card < (leaves (level (complements F) 2) x).card) : x ∈ A := by
  by_contra hxA
  have hsub : leaves (level (complements F) 2) x ⊆ A := by
    intro q hq
    by_contra hqA
    have hp := (Finset.mem_filter.mp hq).2.2
    obtain ⟨hpF,hpc⟩ := Finset.mem_filter.mp hp
    obtain ⟨W,hW,hWeq⟩ := Finset.mem_image.mp hpF
    have hAW : A ⊆ W := by
      intro z hz
      by_contra hzW
      have hzm : z ∈ ({x,q} : Finset (Fin n)) := by
        rw [← hWeq]
        exact Finset.mem_compl.mpr hzW
      simp only [Finset.mem_insert,Finset.mem_singleton] at hzm
      rcases hzm with rfl | rfl
      · exact hxA hz
      · exact hqA hz
    have heq := ha A hA W hW hAW
    have hwc : Wᶜ.card = 2 := by rw [hWeq]; exact hpc
    rw [← heq] at hwc
    simp only [Finset.card_compl,Fintype.card_fin] at hwc
    omega
  have := Finset.card_le_card hsub
  omega

theorem subset_avoiding_leaves {F : Finset (Finset (Fin n))}
    (ha : Antichain F) {A : Finset (Fin n)} (hA : A ∈ F)
    {x : Fin n} (hxA : x ∈ A) (hlarge : 2 < A.card) :
    A ⊆ (leaves (level F 2) x)ᶜ := by
  intro p hp
  apply Finset.mem_compl.mpr
  intro hpL
  have hpF := (Finset.mem_filter.mp (Finset.mem_filter.mp hpL).2.2).1
  have hsub : ({x,p} : Finset (Fin n)) ⊆ A :=
    Finset.insert_subset_iff.mpr ⟨hxA, Finset.singleton_subset_iff.mpr hp⟩
  have heq := ha {x,p} hpF A hA hsub
  have hh := congrArg Finset.card heq
  have hpc : ({x,p} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  omega

theorem erase_not_subset {F : Finset (Finset (Fin n))} (ha : Antichain F)
    {A C : Finset (Fin n)} (hA : A ∈ F) (hC : C ∈ F) {x : Fin n}
    (hxA : x ∈ A) (hne : C.card ≠ A.card) : ¬ C.erase x ⊆ A := by
  intro hsub
  have hCA : C ⊆ A := by
    intro z hz
    by_cases hzx : z = x
    · simpa [hzx] using hxA
    · exact hsub (Finset.mem_erase.mpr ⟨hzx,hz⟩)
  exact hne (congrArg Finset.card (ha C hC A hA hCA))

theorem coatom_blockers_card {C : Finset (Finset (Fin n))}
    {V B D : Finset (Fin n)} (hBV : B ⊆ V) (hDV : D ⊆ V)
    (hC : ∀ A ∈ C, A ⊆ V ∧ A.card+1 = V.card ∧ ¬ B ⊆ A ∧ ¬ D ⊆ A) :
    C.card ≤ (B ∩ D).card := by
  have hsub : C ⊆ (B ∩ D).image (fun b => V.erase b) := by
    intro A hA
    obtain ⟨hAV,hAc,hBA,hDA⟩ := hC A hA
    obtain ⟨b,hbB,hbA⟩ := Finset.not_subset.mp hBA
    have hbV := hBV hbB
    have hAe : A = V.erase b := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact Finset.mem_erase.mpr ⟨fun h => hbA (h ▸ hz),hAV hz⟩
      · rw [Finset.card_erase_of_mem hbV]
        omega
    have hbD : b ∈ D := by
      by_contra hbD
      apply hDA
      rw [hAe]
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun h => hbD (h ▸ hz),hDV hz⟩
    exact Finset.mem_image.mpr ⟨b,Finset.mem_inter.mpr ⟨hbB,hbD⟩,hAe.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem middle_contains_bound (r : ℕ) (hr : 4 ≤ r)
    (F : Finset (Finset (Fin (2*r+2)))) (ha : Antichain F)
    (h2 : r ≤ (level F 2).card) (h3 : 2 ≤ (level F 3).card)
    (hc2 : r ≤ (level (complements F) 2).card) (x : Fin (2*r+2))
    (hx2 : ∀ A ∈ level F 2, x ∈ A)
    (hxc2 : ∀ A ∈ level (complements F) 2, x ∈ A) :
    ((level F (r+1)).filter (fun A => x ∈ A)).card ≤ 1 := by
  let P := leaves (level F 2) x
  let Q := leaves (level (complements F) 2) x
  let V := Pᶜ
  let T := (level F (r+1)).filter (fun A => x ∈ A)
  have hP : r ≤ P.card := by
    dsimp [P]
    rw [card_leaves (E := level F 2) (fun A hA => (Finset.mem_filter.mp hA).2) hx2]
    exact h2
  have hQ : r ≤ Q.card := by
    dsimp [Q]
    rw [card_leaves (E := level (complements F) 2)
      (fun A hA => (Finset.mem_filter.mp hA).2) hxc2]
    exact hc2
  have hV : V.card ≤ r+2 := by
    simp only [V,Finset.card_compl,Fintype.card_fin]
    omega
  have hmem : ∀ A ∈ T, A ∈ F ∧ A.card = r+1 ∧ x ∈ A ∧ A ⊆ V := by
    intro A hA
    obtain ⟨hAl,hAx⟩ := Finset.mem_filter.mp hA
    obtain ⟨hAF,hAc⟩ := Finset.mem_filter.mp hAl
    exact ⟨hAF,hAc,hAx,subset_avoiding_leaves ha hAF hAx (by omega)⟩
  by_cases hsmall : V.card ≤ r+1
  · apply Finset.card_le_one.mpr
    intro A hA B hB
    obtain ⟨_,hAc,_,hAV⟩ := hmem A hA
    obtain ⟨_,hBc,_,hBV⟩ := hmem B hB
    exact (Finset.eq_of_subset_of_card_le hAV (by omega)).trans
      (Finset.eq_of_subset_of_card_le hBV (by omega)).symm
  have hVc : V.card = r+2 := by omega
  obtain ⟨C,hC,D,hD,hCD⟩ := Finset.one_lt_card.mp (by omega : 1 < (level F 3).card)
  obtain ⟨hCF,hCc⟩ := Finset.mem_filter.mp hC
  obtain ⟨hDF,hDc⟩ := Finset.mem_filter.mp hD
  have hxC : x ∈ C := small_contains_center ha hCF x (by omega) (by
    change C.card < Q.card
    omega)
  have hxD : x ∈ D := small_contains_center ha hDF x (by omega) (by
    change D.card < Q.card
    omega)
  have hCV : C ⊆ V := subset_avoiding_leaves ha hCF hxC (by omega)
  have hDV : D ⊆ V := subset_avoiding_leaves ha hDF hxD (by omega)
  have hCe : (C.erase x).card = 2 := by rw [Finset.card_erase_of_mem hxC,hCc]
  have hDe : (D.erase x).card = 2 := by rw [Finset.card_erase_of_mem hxD,hDc]
  have hinter : ((C.erase x) ∩ (D.erase x)).card ≤ 1 := by
    by_contra! hh
    have he1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (show (C.erase x).card ≤ ((C.erase x) ∩ (D.erase x)).card by omega)
    have he2 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      (show (D.erase x).card ≤ ((C.erase x) ∩ (D.erase x)).card by omega)
    have heq := congrArg (fun S : Finset (Fin (2*r+2)) => insert x S) (he1.symm.trans he2)
    exact hCD (by simpa [Finset.insert_erase hxC,Finset.insert_erase hxD] using heq)
  have hbound : T.card ≤ ((C.erase x) ∩ (D.erase x)).card := by
    apply coatom_blockers_card ((Finset.erase_subset x C).trans hCV)
      ((Finset.erase_subset x D).trans hDV)
    intro A hA
    obtain ⟨hAF,hAc,hAx,hAV⟩ := hmem A hA
    exact ⟨hAV,by omega,erase_not_subset ha hAF hCF hAx (by omega),
      erase_not_subset ha hAF hDF hAx (by omega)⟩
  exact hbound.trans hinter

theorem card_complements (F : Finset (Finset (Fin n))) :
    (complements F).card = F.card := by
  apply Finset.card_image_iff.mpr
  intro A hA B hB heq
  simpa using congrArg (fun X : Finset (Fin n) => Xᶜ) heq

/-- The critical obstruction used for the threshold lower bound. -/
theorem critical_size_bound (r : ℕ) (hr : 4 ≤ r)
    (F : Finset (Finset (Fin (2*r+2)))) (ha : Antichain F) (hm : Multiplicity r F) :
    (sizes F).card ≤ 2*r-2 := by
  by_contra! hbad
  have hu := size_count_le (2*r+2) r (by omega) (by omega) F ha hm
  have hs : (sizes F).card = (2*r+2)-3 := by omega
  have hprofile := full_profile (by omega : r+3 ≤ 2*r+2) hr ha hm hs
  have hca := antichain_complements ha
  have hcm := multiplicity_complements hm
  have hcs : (sizes (complements F)).card = (2*r+2)-3 := by
    rw [card_sizes_complements]; exact hs
  have hcprofile := full_profile (by omega : r+3 ≤ 2*r+2) hr hca hcm hcs
  have levels : ∀ k, 2 ≤ k → k ≤ 2*r → r ≤ (level F k).card := by
    intro k hk hkr
    apply level_card_ge hm
    rw [hprofile]
    exact Finset.mem_Icc.mpr ⟨hk,by omega⟩
  have clevels : ∀ k, 2 ≤ k → k ≤ 2*r → r ≤ (level (complements F) k).card := by
    intro k hk hkr
    apply level_card_ge hcm
    rw [hcprofile]
    exact Finset.mem_Icc.mpr ⟨hk,by omega⟩
  have h2 := levels 2 le_rfl (by omega)
  have hc2 := clevels 2 le_rfl (by omega)
  have h3 := levels 3 (by omega) (by omega)
  have hc3 := clevels 3 (by omega) (by omega)
  have hcross : ∀ A ∈ level F 2, ∀ B ∈ level (complements F) 2,
      ¬ Disjoint A B := by
    intro A hA B hB hdis
    obtain ⟨hAF,hAc⟩ := Finset.mem_filter.mp hA
    obtain ⟨hBF,hBc⟩ := Finset.mem_filter.mp hB
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hBF
    have hAC : A ⊆ C := by
      intro z hz
      by_contra hzC
      exact (Finset.disjoint_left.mp hdis hz) (Finset.mem_compl.mpr hzC)
    have heq := congrArg Finset.card (ha A hAF C hC hAC)
    simp only [Finset.card_compl,Fintype.card_fin] at hBc
    omega
  obtain ⟨x,hx,hcx⟩ := common_star
    (fun A hA => (Finset.mem_filter.mp hA).2)
    (fun B hB => (Finset.mem_filter.mp hB).2)
    (hr.trans h2) (hr.trans hc2) hcross
  have hmpos := middle_contains_bound r hr F ha h2 (by omega) hc2 x hx hcx
  have hmcpos := middle_contains_bound r hr (complements F) hca hc2 (by omega)
    (by simpa only [complements_involutive] using h2) x hcx
    (by simpa only [complements_involutive,level] using hx)
  let T := (level F (r+1)).filter (fun A => x ∉ A)
  have hsub : complements T ⊆ (level (complements F) (r+1)).filter (fun A => x ∈ A) := by
    intro B hB
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hAl,hAx⟩ := Finset.mem_filter.mp hA
    obtain ⟨hAF,hAc⟩ := Finset.mem_filter.mp hAl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨A,hAF,rfl⟩,?_⟩,
      Finset.mem_compl.mpr hAx⟩
    simp only [Finset.card_compl,Fintype.card_fin]
    omega
  have hmneg : T.card ≤ 1 := by
    rw [← card_complements T]
    exact (Finset.card_le_card hsub).trans hmcpos
  have hsum := Finset.card_filter_add_card_filter_not (s := level F (r+1))
    (fun A => x ∈ A)
  have hmcard := levels (r+1) (by omega) (by omega)
  change ((level F (r+1)).filter (fun A => x ∉ A)).card ≤ 1 at hmneg
  omega

/-- The finite maximum number of occurring sizes, under the paper's
at-least-r convention. The empty family is included. -/
noncomputable def extremal (n r : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun F : Finset (Finset (Fin n)) =>
    Antichain F ∧ Multiplicity r F)).sup (fun F => (sizes F).card)

theorem extremal_critical_le (r : ℕ) (hr : 4 ≤ r) :
    extremal (2*r+2) r ≤ 2*r-2 := by
  classical
  unfold extremal
  apply Finset.sup_le
  intro F hF
  obtain ⟨ha,hm⟩ := (Finset.mem_filter.mp hF).2
  exact critical_size_bound r hr F ha hm

/-- The eventual equality required in the definition of n₀(r). -/
def IsThreshold (r N : ℕ) : Prop := ∀ n, N < n → extremal n r = n-3

/-- He–Tang Theorem 1.4: every threshold, hence in particular the least
threshold n₀(r), is at least 2r+2. No theorem of threshold existence or of
an upper bound is imported or asserted. -/
theorem threshold_lower_bound (r N : ℕ) (hr : 4 ≤ r) (hN : IsThreshold r N) :
    2*r+2 ≤ N := by
  by_contra! hbad
  have heq := hN (2*r+2) hbad
  have hle := extremal_critical_le r hr
  omega

end JSP000636
