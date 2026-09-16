import JSP000617Nat

/-! Modular near-coverage transferred to integer blocks without wraparound in the block itself. -/
namespace JSP000617

section Lift
variable {p : ℕ} [NeZero p]

def baseBlock (A : Finset (ZMod p × ZMod p)) : Finset ℕ :=
  (Finset.range 2).biUnion (fun i => natTranslate (codedSet A) (i*p))

def coveredResidues (A : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (natSums A).image (fun n => n % M)

omit [NeZero p] in
lemma mem_baseBlock (A : Finset (ZMod p × ZMod p)) {z : ZMod p × ZMod p}
    (hz : z ∈ A) {i : ℕ} (hi : i < 2) : i*p + planeCode z ∈ baseBlock A := by
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_range.mpr hi,?_⟩
  apply Finset.mem_image.mpr
  exact ⟨planeCode z, Finset.mem_image.mpr ⟨z,hz,rfl⟩,rfl⟩

lemma baseBlock_bound (A : Finset (ZMod p × ZMod p)) {a : ℕ} (ha : a ∈ baseBlock A) :
    a < 2*p*p := by
  obtain ⟨i,hi,hai⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hai
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  have hbound := planeCode_bound z
  have hi' := Finset.mem_range.mp hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> simp_all <;> omega

lemma baseBlock_reps_le [Fact p.Prime] (A : Finset (ZMod p × ZMod p)) (R : ℕ)
    (hR : ∀ z, (sumRepresentations A A z).card ≤ R) (n : ℕ) :
    (natReps (baseBlock A) (baseBlock A) n).card ≤ 4*R := by
  calc
    (natReps (baseBlock A) (baseBlock A) n).card ≤
        ∑ ij ∈ Finset.range 2 ×ˢ Finset.range 2,
          (natReps (natTranslate (codedSet A) (ij.1*p))
            (natTranslate (codedSet A) (ij.2*p)) n).card := natReps_biUnion_le _ _ _ _ _
    _ ≤ ∑ _ij ∈ Finset.range 2 ×ˢ Finset.range 2, R := by
      apply Finset.sum_le_sum
      intro ij _hij
      exact (natReps_translate_le _ _ _ _ _).trans (codedSet_reps_le A R hR _)
    _ = 4*R := by simp

lemma baseBlock_sparse (A : Finset (ZMod p × ZMod p)) (C : ℕ)
    (hC : ∀ y, (rowPoints A y).card ≤ C) : locallySparse (baseBlock A) p (6*C) := by
  have h := locallySparse_biUnion (Finset.range 2)
    (fun i => natTranslate (codedSet A) (i*p))
    (fun i _hi => locallySparse_translate (codedSet_sparse A C hC) (i*p))
  simpa [baseBlock,←Nat.mul_assoc] using h

/-- Both half-row positions corresponding to each covered plane point are covered modulo 2p^2. -/
lemma lift_covered [Fact p.Prime] (A : Finset (ZMod p × ZMod p)) {z : ZMod p × ZMod p}
    (hz : z ∈ planeSumset A) {s : ℕ} (hs : s = 1 ∨ s = 2) :
    (planeCode z + s*p) % (2*p*p) ∈ coveredResidues (baseBlock A) (2*p*p) := by
  classical
  obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hz
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  change a+b=z at he
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hx : (a.1.val+b.1.val)%p=z.1.val := by
    rw [←ZMod.val_add]
    exact congrArg (fun z : ZMod p × ZMod p => z.1.val) he
  have hy : (a.2.val+b.2.val)%p=z.2.val := by
    rw [←ZMod.val_add]
    exact congrArg (fun z : ZMod p × ZMod p => z.2.val) he
  let q := (a.1.val+b.1.val)/p
  let r := (a.2.val+b.2.val)/p
  have hxe : a.1.val+b.1.val=z.1.val+p*q := by
    have h := Nat.mod_add_div (a.1.val+b.1.val) p
    rw [hx] at h
    exact h.symm
  have hye : a.2.val+b.2.val=z.2.val+p*r := by
    have h := Nat.mod_add_div (a.2.val+b.2.val) p
    rw [hy] at h
    exact h.symm
  have hq : q ≤ 1 := by
    have ha' := a.1.val_lt
    have hb' := b.1.val_lt
    dsimp [q]
    apply Nat.le_of_lt_succ
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  let t := s-q
  let i := min t 1
  let j := t-i
  have hsbound : 1≤s ∧ s≤2 := by rcases hs with rfl | rfl <;> omega
  have htbound : t≤2 := (Nat.sub_le s q).trans hsbound.2
  have htq : q≤s := by omega
  have hteq : t+q=s := Nat.sub_add_cancel htq
  have hieq : i=min t 1 := rfl
  have hjeq : j=t-i := rfl
  have hi : i < 2 := by omega
  have hj : j < 2 := by omega
  have hij : q+(i+j)=s := by omega
  have hsum : (i*p+planeCode a)+(j*p+planeCode b) =
      (planeCode z+s*p)+(2*p*p)*r := by
    calc
      (i*p+planeCode a)+(j*p+planeCode b) =
          (a.1.val+b.1.val)+p*(i+j)+2*p*(a.2.val+b.2.val) := by simp only [planeCode]; ring
      _ = (z.1.val+p*q)+p*(i+j)+2*p*(z.2.val+p*r) := by rw [hxe,hye]
      _ = (planeCode z+s*p)+(2*p*p)*r := by
        dsimp [planeCode]
        have hh := congrArg (fun n => p*n) hij
        nlinarith
  apply Finset.mem_image.mpr
  refine ⟨(i*p+planeCode a)+(j*p+planeCode b),?_,?_⟩
  · exact Finset.mem_image.mpr ⟨(i*p+planeCode a,j*p+planeCode b),
      Finset.mem_product.mpr ⟨mem_baseBlock A ha hi,mem_baseBlock A hb hj⟩,rfl⟩
  · rw [hsum,Nat.add_mul_mod_self_left]

lemma shiftedCode_injective (s : ℕ) :
    Function.Injective (fun z : ZMod p × ZMod p => (planeCode z+s*p)%(2*p*p)) := by
  intro z w h
  have hz := planeCode_bound z
  have hw := planeCode_bound w
  have hc : (((planeCode z+s*p : ℕ) : ZMod (2*p*p))) =
      (((planeCode w+s*p : ℕ) : ZMod (2*p*p))) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hc
  have he : (planeCode z : ZMod (2*p*p)) = (planeCode w : ZMod (2*p*p)) := add_right_cancel hc
  have hm : planeCode z%(2*p*p)=planeCode w%(2*p*p) := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  rw [Nat.mod_eq_of_lt (show planeCode z<2*p*p by omega),
    Nat.mod_eq_of_lt (show planeCode w<2*p*p by omega)] at hm
  exact planeCode_injective hm

lemma shiftedCode_disjoint (S : Finset (ZMod p × ZMod p)) :
    Disjoint (S.image (fun z => (planeCode z+p)%(2*p*p)))
      (S.image (fun z => (planeCode z+2*p)%(2*p*p))) := by
  apply Finset.disjoint_left.mpr
  intro n hn1 hn2
  obtain ⟨z,hz,h1⟩ := Finset.mem_image.mp hn1
  obtain ⟨w,hw,h2⟩ := Finset.mem_image.mp hn2
  have he := h1.trans h2.symm
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hzp := z.1.val_lt
  have hwp := w.1.val_lt
  have hm := congrArg (fun n => n%(2*p)) he
  have hd : 2*p ∣ 2*p*p := dvd_mul_right _ _
  simp only [Nat.mod_mod_of_dvd _ hd] at hm
  have hzmod : (planeCode z+p)%(2*p)=z.1.val+p := by
    have he : planeCode z+p = z.1.val+p+(2*p)*z.2.val := by simp [planeCode]; ring
    rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  have hwmod : (planeCode w+2*p)%(2*p)=w.1.val := by
    rw [Nat.add_mod_right,code_fst]
  rw [hzmod,hwmod] at hm
  omega

lemma baseBlock_cover_card [Fact p.Prime] (A : Finset (ZMod p × ZMod p)) :
    2*(planeSumset A).card ≤ (coveredResidues (baseBlock A) (2*p*p)).card := by
  classical
  let S := planeSumset A
  let U := S.image (fun z => (planeCode z+p)%(2*p*p))
  let V := S.image (fun z => (planeCode z+2*p)%(2*p*p))
  have hU : U.card=S.card := Finset.card_image_of_injective S (by simpa using shiftedCode_injective (p:=p) 1)
  have hV : V.card=S.card := Finset.card_image_of_injective S (shiftedCode_injective 2)
  have hsub : U ∪ V ⊆ coveredResidues (baseBlock A) (2*p*p) := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      simpa using lift_covered A hz (Or.inl rfl : 1=1 ∨ 1=2)
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      exact lift_covered A hz (Or.inr rfl : 2=1 ∨ 2=2)
  have hd : Disjoint U V := shiftedCode_disjoint S
  have hc := Finset.card_le_card hsub
  have hcard := Finset.card_union_of_disjoint hd
  change 2*S.card ≤ (coveredResidues (baseBlock A) (2*p*p)).card
  omega

end Lift

/-- A genuine natural-number base block, with a quantitative residue near-cover,
a size-independent representation bound, and short-interval sparsity. -/
theorem natural_base_block {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (m : ℕ) :
    ∃ A : Finset ℕ,
      (∀ a ∈ A, a < 2*p*p) ∧
      (coveredResidues A (2*p*p)).card * 2^m ≥ (2^m-1)*(2*p*p) ∧
      (∀ n, (natReps A A n).card ≤ 8*(m+1)^2) ∧
      locallySparse A p (12*(m+1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact Nat.not_dvd_of_pos_of_lt (by omega) hp2 hdiv
  obtain ⟨B,hmiss,hR,hC⟩ := finite_plane_construction_sparse (F:=ZMod p) htwo m
  refine ⟨baseBlock B,fun a ha => baseBlock_bound B ha,?_,?_,?_⟩
  · have hc := baseBlock_cover_card B
    have hS : (planeSumset B).card ≤ p*p := by
      simpa [ZMod.card] using Finset.card_le_univ (planeSumset B)
    have hD : ((Finset.univ : Finset (ZMod p × ZMod p)) \ planeSumset B).card =
        p*p-(planeSumset B).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [ZMod.card]
    rw [hD] at hmiss
    simp only [ZMod.card,pow_two] at hmiss
    have hKe : 1 ≤ 2^m := Nat.one_le_pow m 2 (by omega)
    have hprod := Nat.mul_le_mul_right (2^m) hc
    have hsub : p*p-(planeSumset B).card+(planeSumset B).card=p*p := Nat.sub_add_cancel hS
    have hsubScaled := congrArg (fun z => z*2^m) hsub
    have hKscaled := congrArg (fun z => z*(p*p)) (Nat.sub_add_cancel hKe)
    nlinarith only [hmiss,hprod,hsubScaled,hKscaled]
  · intro n
    have h := baseBlock_reps_le B (2*(m+1)^2) hR n
    nlinarith
  · have h := baseBlock_sparse B (2*(m+1)) hC
    simpa [←Nat.mul_assoc] using h

end JSP000617
