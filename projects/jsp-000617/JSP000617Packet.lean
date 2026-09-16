import JSP000617Lift

/-! Repeated finite blocks with ordinary addition, not modular sumsets. -/
namespace JSP000617

def natPacket (A : Finset ℕ) (M k : ℕ) : Finset ℕ :=
  (Finset.range k).biUnion (fun j => natTranslate A (j*M))

lemma mem_natPacket {A : Finset ℕ} {M k a i : ℕ} (ha : a ∈ A) (hi : i < k) :
    i*M+a ∈ natPacket A M k := by
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,
    Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩

lemma natPacket_bound {A : Finset ℕ} {M k : ℕ}
    (hA : ∀ a ∈ A, a < M) {a : ℕ} (ha : a ∈ natPacket A M k) : a < k*M := by
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
  have hb' := hA b hb
  have hi' := Finset.mem_range.mp hi
  nlinarith

lemma natPacket_reps_le {A : Finset ℕ} {M k R : ℕ}
    (hR : ∀ n, (natReps A A n).card ≤ R) (n : ℕ) :
    (natReps (natPacket A M k) (natPacket A M k) n).card ≤ k^2*R := by
  calc
    (natReps (natPacket A M k) (natPacket A M k) n).card ≤
        ∑ ij ∈ Finset.range k ×ˢ Finset.range k,
          (natReps (natTranslate A (ij.1*M)) (natTranslate A (ij.2*M)) n).card :=
      natReps_biUnion_le _ _ _ _ _
    _ ≤ ∑ _ij ∈ Finset.range k ×ˢ Finset.range k, R :=
      Finset.sum_le_sum (fun ij _hij => (natReps_translate_le _ _ _ _ _).trans (hR _))
    _ = k^2*R := by simp [pow_two]

lemma natPacket_sparse {A : Finset ℕ} {M k d C : ℕ}
    (hC : locallySparse A d C) : locallySparse (natPacket A M k) d (k*C) := by
  have h := locallySparse_biUnion (Finset.range k) (fun i => natTranslate A (i*M))
    (fun i _hi => locallySparse_translate hC (i*M))
  simpa [natPacket] using h

lemma natSums_bound {A : Finset ℕ} {M : ℕ} (hA : ∀ a ∈ A, a < M)
    {n : ℕ} (hn : n ∈ natSums A) : n < 2*M := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
  have ha := hA a (Finset.mem_product.mp hab).1
  have hb := hA b (Finset.mem_product.mp hab).2
  omega

lemma natSums_translate (A : Finset ℕ) (t : ℕ) :
    natSums (natTranslate A t) = (natSums A).image (fun n => 2*t+n) := by
  ext n
  constructor
  · intro hn
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).1
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).2
    exact Finset.mem_image.mpr ⟨a+b,
      Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩,by omega⟩
  · intro hn
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨(t+a,t+b),Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨a,(Finset.mem_product.mp hab).1,rfl⟩,
       Finset.mem_image.mpr ⟨b,(Finset.mem_product.mp hab).2,rfl⟩⟩,by omega⟩

lemma natSums_translate_card (A : Finset ℕ) (t : ℕ) :
    (natSums (natTranslate A t)).card = (natSums A).card := by
  rw [natSums_translate,Finset.card_image_of_injective _ (fun _ _ h => by omega)]

/-- Each covered residue produces 2k-1 distinct ordinary sums in a k-block packet. -/
lemma natPacket_sumset_card {A : Finset ℕ} {M k : ℕ} (hM : 0<M) (hk : 0<k)
    (hA : ∀ a ∈ A, a<M) :
    (coveredResidues A M).card*(2*k-1) ≤ (natSums (natPacket A M k)).card := by
  classical
  let R := coveredResidues A M
  have hex (r : ℕ) : ∃ z : ℕ, r ∈ R → z ∈ natSums A ∧ z%M=r ∧ z<2*M := by
    by_cases hr : r ∈ R
    · obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hr
      exact ⟨z,fun _ => ⟨hz,he,natSums_bound hA hz⟩⟩
    · exact ⟨0,fun h => (hr h).elim⟩
  choose z hz using hex
  let D := R ×ˢ Finset.range (2*k-1)
  let f : ℕ × ℕ → ℕ := fun rs => z rs.1+rs.2*M
  have hf : Set.InjOn f D := by
    rintro ⟨r,s⟩ hrs ⟨u,t⟩ hut he
    have hr := (Finset.mem_product.mp hrs).1
    have hu := (Finset.mem_product.mp hut).1
    have hmod := congrArg (fun n => n%M) he
    change (z r+s*M)%M=(z u+t*M)%M at hmod
    rw [Nat.add_mul_mod_self_right,Nat.add_mul_mod_self_right,(hz r hr).2.1,(hz u hu).2.1] at hmod
    subst u
    change z r+s*M=z r+t*M at he
    have hst : s=t := by nlinarith
    exact Prod.ext rfl hst
  have hsub : D.image f ⊆ natSums (natPacket A M k) := by
    intro n hn
    obtain ⟨⟨r,s⟩,hrs,rfl⟩ := Finset.mem_image.mp hn
    have hr := (Finset.mem_product.mp hrs).1
    have hs := Finset.mem_range.mp (Finset.mem_product.mp hrs).2
    obtain ⟨⟨a,b⟩,hab,hzab⟩ := Finset.mem_image.mp (hz r hr).1
    let i := min s (k-1)
    let j := s-i
    have hi : i<k := by dsimp [i]; omega
    have hj : j<k := by dsimp [j,i]; omega
    have hij : i+j=s := by dsimp [j,i]; omega
    apply Finset.mem_image.mpr
    refine ⟨(i*M+a,j*M+b),Finset.mem_product.mpr
      ⟨mem_natPacket (Finset.mem_product.mp hab).1 hi,
       mem_natPacket (Finset.mem_product.mp hab).2 hj⟩,?_⟩
    dsimp [f]
    change a+b=z r at hzab
    nlinarith
  calc
    R.card*(2*k-1) = D.card := by simp [D]
    _ = (D.image f).card := (Finset.card_image_of_injOn hf).symm
    _ ≤ (natSums (natPacket A M k)).card := Finset.card_le_card hsub

/-- Natural packets of any large prime scale. All constants are independent of p. -/
theorem natural_packet {p : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (m : ℕ) (hK : 4 ≤ 2^m) :
    ∃ Q : Finset ℕ,
      (∀ a ∈ Q, a < (2^m)*(2*p*p)) ∧
      (2^m)*(natSums Q).card ≥ (2^m-2)*(2*(2^m)*(2*p*p)) ∧
      (∀ n, (natReps Q Q n).card ≤ (2^m)^2*(8*(m+1)^2)) ∧
      locallySparse Q p ((2^m)*(12*(m+1))) := by
  obtain ⟨A,hA,hcov,hR,hC⟩ := natural_base_block hp hp2 m
  refine ⟨natPacket A (2*p*p) (2^m),fun a ha => natPacket_bound hA ha,?_,
    natPacket_reps_le hR,natPacket_sparse hC⟩
  have hcard := natPacket_sumset_card (A:=A) (M:=2*p*p) (k:=2^m)
    (by positivity) (by positivity) hA
  have h1 := Nat.mul_le_mul_left (2^m) hcard
  have h2 := Nat.mul_le_mul_right (2*(2^m)-1) hcov
  have hkm1 : (2^m-1)+1=2^m := by omega
  have hkm2 : (2^m-2)+2=2^m := by omega
  have hk2 : (2*(2^m)-1)+1=2*(2^m) := by omega
  have hcoef : (2^m-2)*(2*(2^m)) ≤ (2^m-1)*(2*(2^m)-1) := by
    have he1 : 2^m-1=(2^m-2)+1 := by omega
    have he2 : 2*(2^m)-1=2*(2^m-2)+3 := by omega
    rw [he1,he2]
    have hprod := congrArg (fun z => (2^m-2)*z) hkm2
    nlinarith only [hprod,Nat.zero_le (2^m-2)]
  have hfinal := Nat.mul_le_mul_right (2*p*p) hcoef
  nlinarith only [h1,h2,hfinal]

end JSP000617
