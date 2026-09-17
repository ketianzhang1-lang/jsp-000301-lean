import Threshold

namespace JSP000636
open Finset

/-- Levelwise thinning converts at-least-r multiplicity to exact multiplicity,
without changing the set of occurring sizes. -/
theorem thin_to_exact {n r : ℕ} (hr : 0 < r)
    (F : Finset (Finset (Fin n))) (ha : Antichain F) (hm : Multiplicity r F) :
    ∃ G ⊆ F, Antichain G ∧ ExactMultiplicity r G ∧ sizes G = sizes F := by
  classical
  have hpick : ∀ t : ↥(sizes F), ∃ S : Finset (Finset (Fin n)),
      S ⊆ F.filter (fun A => A.card = t.val) ∧ S.card = r := by
    intro t
    obtain ⟨A,hA,hAt⟩ := mem_image.mp t.property
    apply exists_subset_card_eq
    have hh := hm A hA
    simpa only [hAt] using hh
  choose pick hp hc using hpick
  let G := univ.biUnion pick
  have hGF : G ⊆ F := by
    intro A hA
    obtain ⟨t,_,hAt⟩ := mem_biUnion.mp hA
    exact (mem_filter.mp (hp t hAt)).1
  have heq : ∀ t : ↥(sizes F), G.filter (fun A => A.card = t.val) = pick t := by
    intro t
    ext A
    constructor
    · intro hA
      obtain ⟨hAG,hcard⟩ := mem_filter.mp hA
      obtain ⟨s,_,hAs⟩ := mem_biUnion.mp hAG
      have hs := (mem_filter.mp (hp s hAs)).2
      have hst : s = t := Subtype.ext (hs.symm.trans hcard)
      subst s
      exact hAs
    · intro hA
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨t,mem_univ _,hA⟩,
        (mem_filter.mp (hp t hA)).2⟩
  have hsizes : sizes G = sizes F := by
    apply Subset.antisymm (image_subset_image hGF)
    intro k hk
    let t : ↥(sizes F) := ⟨k,hk⟩
    have hpos : 0 < (pick t).card := by rw [hc]; exact hr
    obtain ⟨A,hA⟩ := card_pos.mp hpos
    apply mem_image.mpr
    exact ⟨A,mem_biUnion.mpr ⟨t,mem_univ _,hA⟩,(mem_filter.mp (hp t hA)).2⟩
  refine ⟨G,hGF,?_,?_,hsizes⟩
  · intro A hA B hB hsub
    exact ha A (hGF hA) B (hGF hB) hsub
  · intro A hA
    let t : ↥(sizes F) := ⟨A.card,mem_image.mpr ⟨A,hGF hA,rfl⟩⟩
    have hh := congrArg Finset.card (heq t)
    simpa only [hc] using hh

/-- The attaining construction also satisfies the problem's exact-r convention. -/
theorem exact_attaining_family (n r : ℕ) (hr : 2 ≤ r)
    (hn : 2*r+4*Nat.sqrt r+8 ≤ n) :
    ∃ F : Finset (Finset (Fin n)),
      Antichain F ∧ ExactMultiplicity r F ∧
      (sizes F).card = n-3 ∧ F.card = r*(n-3) := by
  obtain ⟨F,ha,hm,hs⟩ := attaining_family n r hr hn
  obtain ⟨G,_,hGa,hGe,hGs⟩ := thin_to_exact (by omega) F ha hm
  refine ⟨G,hGa,hGe,by rw [hGs,hs],?_⟩
  rw [card_eq_mul_size_count hGe,hGs,hs]

end JSP000636
