import Upper

namespace JSP000636
open Finset

/-- Assemble separated tags and payloads around a common point. -/
noncomputable def assembleHalf {n r k d : ℕ} (hn : 0 < n)
    (C B : Fin (k-1) → Fin r → Finset (Fin n))
    (hC : ∀ t j x, x ∈ C t j → 0 < x.val ∧ x.val < d)
    (hB : ∀ t j x, x ∈ B t j → d ≤ x.val)
    (hd : 0 < d)
    (hcard : ∀ t j, (C t j).card + (B t j).card = t.val+1)
    (htag : ∀ t j s i, C t j ⊆ C s i → t = s)
    (hinj : ∀ t i j, C t i = C t j → B t i = B t j → i = j) :
    HalfFamily n r k := by
  classical
  let a : Fin n := ⟨0,hn⟩
  let f := fun t j => insert a (C t j ∪ B t j)
  have hzero : ∀ t j, a ∉ C t j ∪ B t j := by
    intro t j ha
    rcases mem_union.mp ha with ha | ha
    · have := (hC t j a ha).1; simp [a] at this
    · have := hB t j a ha; dsimp [a] at this; omega
  have hdis : ∀ t j, Disjoint (C t j) (B t j) := by
    intro t j
    apply disjoint_left.mpr
    intro x hx hy
    have := (hC t j x hx).2
    have := hB t j x hy
    omega
  have hc : ∀ t j, (f t j).card = t.val+2 := by
    intro t j
    dsimp [f]
    rw [card_insert_of_notMem (hzero t j), card_union_of_disjoint (hdis t j), hcard]
  have extractC : ∀ t j s i, f t j ⊆ f s i → C t j ⊆ C s i := by
    intro t j s i hsub x hx
    have hmem := hsub (mem_insert_of_mem (mem_union_left _ hx))
    rcases mem_insert.mp hmem with hx0 | hxmem
    · have := (hC t j x hx).1; subst x; simp [a] at this
    · rcases mem_union.mp hxmem with h | h
      · exact h
      · have := (hC t j x hx).2; have := hB s i x h; omega
  have extractB : ∀ t j s i, f t j ⊆ f s i → B t j ⊆ B s i := by
    intro t j s i hsub x hx
    have hmem := hsub (mem_insert_of_mem (mem_union_right _ hx))
    rcases mem_insert.mp hmem with hx0 | hxmem
    · have := hB t j x hx; subst x; dsimp [a] at this; omega
    · rcases mem_union.mp hxmem with h | h
      · have := hB t j x hx; have := (hC s i x h).2; omega
      · exact h
  refine ⟨a, f, hc, ?_, ?_, ?_⟩
  · intro t i j hij
    apply hinj t i j
    · exact Subset.antisymm (extractC t i t j hij.le) (extractC t j t i hij.ge)
    · exact Subset.antisymm (extractB t i t j hij.le) (extractB t j t i hij.ge)
  · intro t j; exact mem_insert_self _ _
  · intro t j s i hsub
    have hts := htag t j s i (extractC t j s i hsub)
    subst s
    exact eq_of_subset_of_card_le hsub (by rw [hc,hc])



/-- A half-family exists whenever enough two-element labels are available. -/
theorem pairLabel_half_exists (n r k : ℕ) (hr : 2 ≤ r)
    (hk : r+4 ≤ k) (hn : 2*k ≤ n)
    (hcap : k-3 ≤ (k-r).choose 2) : Nonempty (HalfFamily n r k) := by
  classical
  let p : Fin r → Fin n := fun j => ⟨j.val+1,by have := j.isLt; omega⟩
  let u : Fin n := ⟨r+1,by omega⟩
  let v0 : Fin n := ⟨r+2,by omega⟩
  let v1 : Fin n := ⟨k+2,by omega⟩
  let V := Ico v0 v1
  let R := Ici v1
  have cardV : V.card = k-r := by simp [V,v0,v1,Fin.card_Ico]
  have cardR : R.card = n-k-2 := by simp [R,v1,Fin.card_Ici, Nat.sub_sub]
  have memV : ∀ x, x ∈ V → r+2 ≤ x.val ∧ x.val < k+2 := by
    intro x hx
    have hh : v0 ≤ x ∧ x < v1 := mem_Ico.mp hx
    exact hh
  have memR : ∀ x, x ∈ R → k+2 ≤ x.val := by
    intro x hx
    have hh : v1 ≤ x := mem_Ici.mp hx
    exact hh
  obtain ⟨L,hLi,hL⟩ := select_subsets V (k-3) 2 (by simpa [cardV] using hcap)
  have hBs : ∀ t : Fin (k-3), ∃ b : Fin r → Finset (Fin n),
      Function.Injective b ∧ ∀ j, b j ⊆ R ∧ (b j).card = t.val+1 := by
    intro t
    apply select_subsets
    have ht := t.isLt
    have hcr : r ≤ R.card := by rw [cardR]; omega
    exact hcr.trans (choose_ge_self (by omega) (by rw [cardR]; omega))
  choose b hbi hb using hBs
  let z : Fin (k-3) := ⟨0,by omega⟩
  let C := fun (t : Fin (k-1)) (j : Fin r) =>
    if h0 : t.val = 0 then {p j}
    else if h1 : t.val = 1 then {u}
    else L ⟨t.val-2,by have := t.isLt; omega⟩
  let B := fun (t : Fin (k-1)) (j : Fin r) =>
    if h0 : t.val = 0 then ∅
    else if h1 : t.val = 1 then b z j
    else b ⟨t.val-2,by have := t.isLt; omega⟩ j
  have hC : ∀ t j x, x ∈ C t j → 0 < x.val ∧ x.val < k+2 := by
    intro t j x hx
    dsimp [C] at hx
    split_ifs at hx with h0 h1
    · have hx' := mem_singleton.mp hx; subst x
      dsimp [p]; have := j.isLt; omega
    · have hx' := mem_singleton.mp hx; subst x
      dsimp [u]; omega
    · have h := memV x ((hL _).1 hx); omega
  have hB : ∀ t j x, x ∈ B t j → k+2 ≤ x.val := by
    intro t j x hx
    dsimp [B] at hx
    split_ifs at hx with h0 h1
    · exact False.elim (notMem_empty _ hx)
    · exact memR x ((hb z j).1 hx)
    · exact memR x ((hb _ j).1 hx)
  have hcard : ∀ t j, (C t j).card + (B t j).card = t.val+1 := by
    intro t j
    dsimp [C,B]
    split_ifs with h0 h1
    · simp [h0]
    · rw [(hb z j).2]; simp [h1,z]
    · rw [(hL _).2, (hb _ j).2]; dsimp; have := t.isLt; omega
  have htag : ∀ t j s i, C t j ⊆ C s i → t = s := by
    intro t j s i hsub
    dsimp [C] at hsub
    split_ifs at hsub with ht0 ht1 hs0 hs1
    · apply Fin.ext; omega
    · have hmem := hsub (mem_singleton_self _)
      have heq := mem_singleton.mp hmem
      have he := congrArg Fin.val heq
      dsimp [p,u] at he; have := j.isLt; omega
    · have hmem := hsub (mem_singleton_self _)
      have hv := memV (p j) ((hL _).1 hmem)
      dsimp [p] at hv; have := j.isLt; omega
    · have hmem := hsub (mem_singleton_self _)
      have heq := mem_singleton.mp hmem
      have he := congrArg Fin.val heq
      dsimp [p,u] at he; have := i.isLt; omega
    · apply Fin.ext; omega
    · have hmem := hsub (mem_singleton_self _)
      have hv := memV u ((hL _).1 hmem)
      dsimp [u] at hv; omega
    · have hh := card_le_card hsub
      rw [(hL _).2, card_singleton] at hh; omega
    · have hh := card_le_card hsub
      rw [(hL _).2, card_singleton] at hh; omega
    · have heq := eq_of_subset_of_card_le hsub (by rw [(hL _).2,(hL _).2])
      have he := congrArg Fin.val (hLi heq)
      apply Fin.ext
      dsimp at he
      omega
  have hinj : ∀ t i j, C t i = C t j → B t i = B t j → i = j := by
    intro t i j hce hbe
    dsimp [C] at hce
    dsimp [B] at hbe
    split_ifs at hce hbe with ht0 ht1
    · have hp : p i = p j := singleton_injective hce
      apply Fin.ext
      have := congrArg Fin.val hp
      dsimp [p] at this; omega
    · exact hbi z hbe
    · exact hbi _ hbe
  exact ⟨assembleHalf (by omega) C B hC hB (by omega) hcard htag hinj⟩

end JSP000636
