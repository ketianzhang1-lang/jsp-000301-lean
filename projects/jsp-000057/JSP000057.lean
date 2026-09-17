/-
Copyright 2026 Ketian Zhang. Licensed under Apache-2.0.
Prepared with OpenAI Codex. This formalizes a classical rank-two special case
of the sunflower problem, not the general sunflower conjecture.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace JSP000057

variable {α : Type*} [DecidableEq α]

def Sunflower (S : Finset (Finset α)) : Prop :=
  ∃ C : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

def degree (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter fun A => x ∈ A).card

lemma inter_eq_singleton {A B : Finset α} {x : α}
    (hA : A.card = 2) (hB : B.card = 2) (hxA : x ∈ A) (hxB : x ∈ B)
    (hne : A ≠ B) : A ∩ B = {x} := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hyA, hyB⟩
    by_contra hy
    have hp : ({x, y} : Finset α).card = 2 := by simp [Ne.symm hy]
    have heA : ({x, y} : Finset α) = A :=
      Finset.eq_of_subset_of_card_le (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hxA hyA) (by omega)
    have heB : ({x, y} : Finset α) = B :=
      Finset.eq_of_subset_of_card_le (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hxB hyB) (by omega)
    exact hne (heA.symm.trans heB)
  · rintro rfl
    exact ⟨hxA, hxB⟩

lemma sunflower_of_large_degree (F : Finset (Finset α))
    (hu : ∀ A ∈ F, A.card = 2) (x : α) (k : ℕ) (hk : k ≤ degree F x) :
    ∃ S ⊆ F, S.card = k ∧ Sunflower S := by
  obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq hk
  refine ⟨S, hS.trans (Finset.filter_subset _ _), hc, {x}, ?_⟩
  intro A hA B hB hne
  have ha := Finset.mem_filter.mp (hS hA)
  have hb := Finset.mem_filter.mp (hS hB)
  exact inter_eq_singleton (hu A ha.1) (hu B hb.1) ha.2 hb.2 hne

lemma intersecting_card_le_three (F : Finset (Finset α))
    (hd : ∀ x, degree F x ≤ 2) (A : Finset α) (hAF : A ∈ F) (hA : A.card = 2) :
    (F.filter fun B => ¬Disjoint A B).card ≤ 3 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
  let Fa := F.filter fun B => a ∈ B
  let Fb := F.filter fun B => b ∈ B
  have he : (F.filter fun B => ¬Disjoint ({a, b} : Finset α) B) = Fa ∪ Fb := by
    ext B
    simp [Fa, Fb, Finset.disjoint_left]
    tauto
  have ha : Fa.card ≤ 2 := hd a
  have hb : Fb.card ≤ 2 := hd b
  have hi : 1 ≤ (Fa ∩ Fb).card := by
    apply Finset.one_le_card.mpr
    exact ⟨{a, b}, by simp [Fa, Fb, hAF]⟩
  have hc := Finset.card_union_add_card_inter Fa Fb
  rw [he]
  omega

/-- Greedy matching with at most three deleted edges per choice. -/
theorem matching_of_card (r : ℕ) (F : Finset (Finset α))
    (hu : ∀ A ∈ F, A.card = 2) (hd : ∀ x, degree F x ≤ 2)
    (hc : 3 * r < F.card) :
    ∃ S ⊆ F, S.card = r + 1 ∧ (S : Set (Finset α)).PairwiseDisjoint id := by
  induction r generalizing F with
  | zero =>
    obtain ⟨A, hA⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    exact ⟨{A}, by simpa, by simp, by simp⟩
  | succ r ih =>
    classical
    obtain ⟨A, hAF⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    let G := F.filter fun B => Disjoint A B
    have hGF : G ⊆ F := Finset.filter_subset _ _
    have hGu : ∀ B ∈ G, B.card = 2 := fun B hB => hu B (hGF hB)
    have hGd : ∀ x, degree G x ≤ 2 := by
      intro x
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hGF)).trans (hd x)
    have hsize := Finset.card_filter_add_card_filter_not (s := F) (p := fun B => Disjoint A B)
    have hrem := intersecting_card_le_three F hd A hAF (hu A hAF)
    have hGc : 3 * r < G.card := by dsimp [G]; omega
    obtain ⟨S, hSG, hSc, hSd⟩ := ih G hGu hGd hGc
    have hAn : A ∉ S := by
      intro hAS
      have hself := (Finset.mem_filter.mp (hSG hAS)).2
      have hz : A = ∅ := disjoint_self.mp hself
      have ht := hu A hAF
      simp [hz] at ht
    refine ⟨insert A S, Finset.insert_subset hAF (hSG.trans hGF), ?_, ?_⟩
    · simp [hAn, hSc, Nat.add_assoc]
    · rw [Finset.coe_insert]
      apply hSd.insert
      intro B hB _
      exact (Finset.mem_filter.mp (hSG hB)).2

/-- Seven distinct two-element sets force a three-petal sunflower. -/
theorem seven_forces_three (F : Finset (Finset α))
    (hu : ∀ A ∈ F, A.card = 2) (hc : 7 ≤ F.card) :
    ∃ S ⊆ F, S.card = 3 ∧ Sunflower S := by
  classical
  by_cases h : ∃ x, 3 ≤ degree F x
  · obtain ⟨x, hx⟩ := h
    exact sunflower_of_large_degree F hu x 3 hx
  · have hd : ∀ x, degree F x ≤ 2 := by push Not at h; intro x; have := h x; omega
    obtain ⟨S, hSF, hSc, hSd⟩ := matching_of_card 2 F hu hd (by omega)
    refine ⟨S, hSF, hSc, ∅, ?_⟩
    intro A hA B hB hne
    exact Finset.disjoint_iff_inter_eq_empty.mp (hSd hA hB hne)

/-- The six edges of two disjoint triangles. -/
def twoTriangles : Finset (Finset ℕ) :=
  {{0, 1}, {0, 2}, {1, 2}, {3, 4}, {3, 5}, {4, 5}}

theorem twoTriangles_card : twoTriangles.card = 6 := by decide

theorem twoTriangles_uniform : ∀ A ∈ twoTriangles, A.card = 2 := by decide

theorem twoTriangles_triple_obstruction :
    ∀ A ∈ twoTriangles, ∀ B ∈ twoTriangles, ∀ C ∈ twoTriangles,
      A ≠ B → A ≠ C → B ≠ C → ¬(A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) := by
  decide

theorem twoTriangles_no_three (S : Finset (Finset ℕ))
    (hS : S ⊆ twoTriangles) (hc : S.card = 3) : ¬ Sunflower S := by
  obtain ⟨A, B, C, hAB, hAC, hBC, rfl⟩ := Finset.card_eq_three.mp hc
  rintro ⟨K, hK⟩
  have hA : A ∈ ({A, B, C} : Finset (Finset ℕ)) := by simp
  have hB : B ∈ ({A, B, C} : Finset (Finset ℕ)) := by simp
  have hC : C ∈ ({A, B, C} : Finset (Finset ℕ)) := by simp
  exact twoTriangles_triple_obstruction A (hS hA) B (hS hB) C (hS hC)
    hAB hAC hBC ⟨(hK A hA B hB hAB).trans (hK A hA C hC hAC).symm,
      (hK A hA B hB hAB).trans (hK B hB C hC hBC).symm⟩

/-- Exact finite-family threshold, uniformly over every ground type. -/
theorem threshold_iff (m : ℕ) :
    (∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = 2) → m ≤ F.card →
      ∃ S ⊆ F, S.card = 3 ∧ Sunflower S) ↔ 7 ≤ m := by
  constructor
  · intro h
    by_contra hm
    obtain ⟨S, hS, hc, hs⟩ := h ℕ twoTriangles twoTriangles_uniform (by
      rw [twoTriangles_card]; omega)
    exact twoTriangles_no_three S hS hc hs
  · intro hm α _ F hu hc
    exact seven_forces_three F hu (hm.trans hc)

end JSP000057

/- The following three definitions are reproduced from Formal Conjectures
at 40e7c98697de6f66b8cbdbf641749ab39ed9c152, Apache-2.0.
Copyright 2025-2026 The Formal Conjectures Authors. -/

def IsSunflowerWithKernel {α : Type*} (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

def IsSunflower {α : Type*} (F : Set (Set α)) : Prop :=
  ∃ S, IsSunflowerWithKernel F S

namespace Erdos20

noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

end Erdos20

namespace JSP000057

variable {α : Type*} [DecidableEq α]

def setFamily (F : Finset (Finset α)) : Set (Set α) :=
  (fun A : Finset α => (A : Set α)) '' (F : Set (Finset α))

omit [DecidableEq α] in
lemma setFamily_ncard (F : Finset (Finset α)) : (setFamily F).ncard = F.card := by
  rw [setFamily, Set.ncard_image_of_injective _ Finset.coe_injective]
  exact Set.ncard_coe_finset F

omit [DecidableEq α] in
lemma mem_setFamily (F : Finset (Finset α)) (A : Finset α) :
    (A : Set α) ∈ setFamily F ↔ A ∈ F := by
  constructor
  · rintro ⟨B, hB, he⟩
    exact Finset.coe_injective he ▸ hB
  · intro hA
    exact ⟨A, hA, rfl⟩

lemma sunflower_setFamily_iff (F : Finset (Finset α)) :
    IsSunflower (setFamily F) ↔ Sunflower F := by
  classical
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨(F.biUnion id).filter fun x => x ∈ K, ?_⟩
    intro A hA B hB hne
    have he := hK ((mem_setFamily F A).mpr hA) ((mem_setFamily F B).mpr hB)
      (fun h => hne (Finset.coe_injective h))
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨Finset.mem_biUnion.mpr ⟨A, hA, hx.1⟩, he ▸ hx⟩
    · intro hx
      have : x ∈ (A : Set α) ∩ (B : Set α) := he.symm ▸ hx.2
      exact this
  · rintro ⟨K, hK⟩
    refine ⟨(K : Set α), ?_⟩
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    have he := hK A hA B hB (fun h => hne (congrArg (fun X : Finset α => (X : Set α)) h))
    exact (Finset.coe_inter A B).symm.trans (congrArg (fun X : Finset α => (X : Set α)) he)

lemma realize_family (F : Set (Set α)) (hF : F.Finite)
    (hfin : ∀ A ∈ F, A.Finite) :
    ∃ G : Finset (Finset α), setFamily G = F := by
  classical
  let ft : Set α → Finset α := fun A => if h : A.Finite then h.toFinset else ∅
  have hcoe : ∀ A ∈ F, (ft A : Set α) = A := by
    intro A hA
    simp [ft, hfin A hA]
  refine ⟨hF.toFinset.image ft, ?_⟩
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    have hCF : C ∈ F := by simpa using hC
    simpa [hcoe C hCF] using hCF
  · intro hA
    exact ⟨ft A, Finset.mem_image.mpr ⟨A, by simpa using hA, rfl⟩, hcoe A hA⟩

theorem seven_forces_three_sets (F : Set (Set α))
    (hu : ∀ A ∈ F, A.ncard = 2) (hc : 7 ≤ F.ncard) :
    ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S := by
  classical
  have hF : F.Finite := Set.finite_of_ncard_ne_zero (by omega)
  obtain ⟨G, rfl⟩ := realize_family F hF (fun A hA =>
    Set.finite_of_ncard_ne_zero (by rw [hu A hA]; decide))
  have hGu : ∀ A ∈ G, A.card = 2 := by
    intro A hA
    simpa using hu A ((mem_setFamily G A).mpr hA)
  obtain ⟨S, hSG, hSc, hSun⟩ := seven_forces_three G hGu (by
    simpa [setFamily_ncard] using hc)
  refine ⟨setFamily S, ?_, by rw [setFamily_ncard, hSc], (sunflower_setFamily_iff S).mpr hSun⟩
  rintro _ ⟨A, hA, rfl⟩
  exact (mem_setFamily G A).mpr (hSG hA)

theorem twoTriangles_sets_no_three (S : Set (Set ℕ))
    (hS : S ⊆ setFamily twoTriangles) (hc : S.ncard = 3) : ¬ IsSunflower S := by
  classical
  intro hs
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have helements : ∀ A ∈ S, A.Finite := by
    intro A hA
    obtain ⟨B, _, rfl⟩ := hS hA
    exact B.finite_toSet
  obtain ⟨G, rfl⟩ := realize_family S hfin helements
  have hG : G ⊆ twoTriangles := by
    intro A hA
    exact (mem_setFamily twoTriangles A).mp (hS ((mem_setFamily G A).mpr hA))
  exact twoTriangles_no_three G hG (by simpa [setFamily_ncard] using hc)
    ((sunflower_setFamily_iff G).mp hs)

/-- The exact predicate appearing under the infimum in the original definition. -/
theorem original_threshold_iff (m : ℕ) :
    (∀ {α : Type}, ∀ (F : Set (Set α)),
      ((∀ A ∈ F, A.ncard = 2) ∧ m ≤ F.ncard) →
        ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S) ↔ 7 ≤ m := by
  classical
  constructor
  · intro h
    by_contra hm
    have hwu : ∀ A ∈ setFamily twoTriangles, A.ncard = 2 := by
      rintro _ ⟨A, hA, rfl⟩
      simpa using twoTriangles_uniform A hA
    have hwc : m ≤ (setFamily twoTriangles).ncard := by
      rw [setFamily_ncard, twoTriangles_card]
      omega
    obtain ⟨S, hS, hc, hs⟩ := h (setFamily twoTriangles) ⟨hwu, hwc⟩
    exact twoTriangles_sets_no_three S hS hc hs
  · intro hm α F hF
    exact seven_forces_three_sets F hF.1 (hm.trans hF.2)

/-- Sharp two-uniform, three-petal sunflower threshold, in the original notation. -/
theorem f_two_three : Erdos20.f 2 3 = 7 := by
  apply IsLeast.csInf_eq
  constructor
  · exact (original_threshold_iff 7).mpr le_rfl
  · intro m hm
    exact (original_threshold_iff m).mp hm

end JSP000057
