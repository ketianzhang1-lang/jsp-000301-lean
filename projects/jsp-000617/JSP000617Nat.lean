import JSP000617Sparse

/-!
The transfer from finite planes to ordinary natural-number addition.
These lemmas retain the actual ordered representation function and explicitly
control carries. This file is part of the new JSP-000617 development.
-/
namespace JSP000617

/-- Ordered pairs with a prescribed ordinary natural-number sum. -/
def natReps (A B : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter (fun ab => ab.1 + ab.2 = n)

def natSums (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun ab => ab.1 + ab.2)

def natTranslate (A : Finset ℕ) (t : ℕ) : Finset ℕ :=
  A.image (fun a => t + a)

/-- Every two points are at distance at most d. -/
def smallDiameter (S : Finset ℕ) (d : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≤ y + d

/-- A form of short-interval sparsity preserved under arbitrary translations. -/
def locallySparse (A : Finset ℕ) (d C : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → smallDiameter S d → S.card ≤ C

lemma natReps_translate_le (A B : Finset ℕ) (t u n : ℕ) :
    (natReps (natTranslate A t) (natTranslate B u) n).card ≤
      (natReps A B (n - (t + u))).card := by
  classical
  have hsub : natReps (natTranslate A t) (natTranslate B u) n ⊆
      (natReps A B (n - (t + u))).image (fun ab => (t + ab.1, u + ab.2)) := by
    rintro ⟨a,b⟩ hab
    obtain ⟨hm,he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hm
    obtain ⟨a0,ha0,haeq⟩ := Finset.mem_image.mp ha
    obtain ⟨b0,hb0,hbeq⟩ := Finset.mem_image.mp hb
    change t+a0=a at haeq
    change u+b0=b at hbeq
    subst a b
    exact Finset.mem_image.mpr ⟨(a0,b0),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha0,hb0⟩,by omega⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma natReps_biUnion_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (A : ι → Finset ℕ) (B : κ → Finset ℕ) (n : ℕ) :
    (natReps (I.biUnion A) (J.biUnion B) n).card ≤
      ∑ ij ∈ I ×ˢ J, (natReps (A ij.1) (B ij.2) n).card := by
  classical
  have hs : natReps (I.biUnion A) (J.biUnion B) n ⊆
      (I ×ˢ J).biUnion (fun ij => natReps (A ij.1) (B ij.2) n) := by
    rintro ⟨a,b⟩ hab
    obtain ⟨hm,he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hm
    obtain ⟨i,hi,hai⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j,hj,hbj⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hi,hj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hai,hbj⟩,he⟩⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le

lemma locallySparse_translate {A : Finset ℕ} {d C : ℕ}
    (hA : locallySparse A d C) (t : ℕ) : locallySparse (natTranslate A t) d C := by
  classical
  intro S hS hdiam
  let U := A.filter (fun a => t + a ∈ S)
  have hsub : S ⊆ U.image (fun a => t + a) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hS hx)
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hx⟩,rfl⟩
  have hU : U.card ≤ C := hA U (Finset.filter_subset _ _) (by
    intro a ha b hb
    have hh := hdiam (t+a) (Finset.mem_filter.mp ha).2
      (t+b) (Finset.mem_filter.mp hb).2
    omega)
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hU)

lemma locallySparse_biUnion {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) {d C : ℕ}
    (hA : ∀ i ∈ I, locallySparse (A i) d C) :
    locallySparse (I.biUnion A) d (I.card * C) := by
  classical
  intro S hS hdiam
  have hs : S ⊆ I.biUnion (fun i => S ∩ A i) := by
    intro a ha
    obtain ⟨i,hi,hai⟩ := Finset.mem_biUnion.mp (hS ha)
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_inter.mpr ⟨ha,hai⟩⟩
  calc
    S.card ≤ (I.biUnion (fun i => S ∩ A i)).card := Finset.card_le_card hs
    _ ≤ ∑ i ∈ I, (S ∩ A i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, C := by
      apply Finset.sum_le_sum
      intro i hi
      apply hA i hi (S ∩ A i) Finset.inter_subset_right
      intro a ha b hb
      exact hdiam a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
    _ = I.card * C := by simp

section Encoding
variable {p : ℕ} [NeZero p]

/-- Base 2p separates the first-coordinate sums, so exact sums cannot carry. -/
def planeCode (z : ZMod p × ZMod p) : ℕ := z.1.val + 2*p*z.2.val

def codedSet (A : Finset (ZMod p × ZMod p)) : Finset ℕ := A.image planeCode

lemma planeCode_bound (z : ZMod p × ZMod p) : planeCode z + p < 2*p*p := by
  have hx := z.1.val_lt
  have hy := z.2.val_lt
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  dsimp [planeCode]
  nlinarith

lemma code_fst (z : ZMod p × ZMod p) : planeCode z % (2*p) = z.1.val := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hx := z.1.val_lt
  simp [planeCode, Nat.add_mod, Nat.mod_eq_of_lt (show z.1.val < 2*p by omega)]

lemma code_snd (z : ZMod p × ZMod p) : planeCode z / (2*p) = z.2.val := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hx := z.1.val_lt
  rw [planeCode, Nat.add_mul_div_left _ _ (show 0<2*p by omega),
    Nat.div_eq_of_lt (show z.1.val < 2*p by omega), Nat.zero_add]

lemma planeCode_injective : Function.Injective (@planeCode p) := by
  intro z w he
  apply Prod.ext
  · apply ZMod.val_injective p
    simpa only [code_fst] using congrArg (fun n => n % (2*p)) he
  · apply ZMod.val_injective p
    simpa only [code_snd] using congrArg (fun n => n / (2*p)) he

lemma code_sum_coordinates {a b c d : ZMod p × ZMod p}
    (h : planeCode a + planeCode b = planeCode c + planeCode d) :
    a + b = c + d := by
  have hxa := a.1.val_lt
  have hxb := b.1.val_lt
  have hxc := c.1.val_lt
  have hxd := d.1.val_lt
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hm := congrArg (fun n => n % (2*p)) h
  have hn (z w : ZMod p × ZMod p) :
      (planeCode z + planeCode w) % (2*p) = z.1.val + w.1.val := by
    have hz := z.1.val_lt
    have hw := w.1.val_lt
    have he : planeCode z + planeCode w = (z.1.val + w.1.val) + 2*p*(z.2.val+w.2.val) := by
      simp only [planeCode]; ring
    rw [he, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hn,hn] at hm
  have hs : a.2.val + b.2.val = c.2.val + d.2.val := by
    dsimp [planeCode] at h
    nlinarith
  apply Prod.ext
  · have hc := congrArg (fun n : ℕ => (n : ZMod p)) hm
    simpa using hc
  · have hc := congrArg (fun n : ℕ => (n : ZMod p)) hs
    simpa using hc

lemma codedSet_reps_le [Fact p.Prime] (A : Finset (ZMod p × ZMod p)) (R : ℕ)
    (hR : ∀ z, (sumRepresentations A A z).card ≤ R) (n : ℕ) :
    (natReps (codedSet A) (codedSet A) n).card ≤ R := by
  classical
  by_cases he : (natReps (codedSet A) (codedSet A) n).Nonempty
  · obtain ⟨⟨a,b⟩,hab⟩ := he
    obtain ⟨hm,hsum⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hm
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    have hsub : natReps (codedSet A) (codedSet A) n ⊆
        (sumRepresentations A A (x+y)).image (fun uv => (planeCode uv.1,planeCode uv.2)) := by
      rintro ⟨a,b⟩ hab
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hm
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨(u,v),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,
          code_sum_coordinates (he.trans hsum.symm)⟩,rfl⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (hR (x+y)))
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]

lemma codedSet_sparse (A : Finset (ZMod p × ZMod p)) (C : ℕ)
    (hC : ∀ y, (rowPoints A y).card ≤ C) : locallySparse (codedSet A) p (3*C) := by
  classical
  intro S hS hd
  by_cases he : S.Nonempty
  · obtain ⟨a,ha⟩ := he
    obtain ⟨z,hz,hcode⟩ := Finset.mem_image.mp (hS ha)
    let rows : Finset (ZMod p) := {((z.2.val-1 : ℕ) : ZMod p),z.2,((z.2.val+1 : ℕ) : ZMod p)}
    have hs : S ⊆ (rows.biUnion (rowPoints A)).image planeCode := by
      intro b hb
      obtain ⟨w,hw,hwcode⟩ := Finset.mem_image.mp (hS hb)
      have h1 := hd a ha b hb
      have h2 := hd b hb a ha
      rw [←hcode,←hwcode] at h1 h2
      have hx := z.1.val_lt
      have hy := w.1.val_lt
      have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
      have hrow : w.2.val + 1 ≥ z.2.val ∧ w.2.val ≤ z.2.val + 1 := by
        dsimp [planeCode] at h1 h2
        constructor <;> nlinarith
      have hchoices : w.2.val = z.2.val-1 ∨ w.2.val = z.2.val ∨ w.2.val = z.2.val+1 := by omega
      have hr : w.2 ∈ rows := by
        rcases hchoices with h | h | h
        · have hcast := congrArg (fun n : ℕ => (n : ZMod p)) h
          simp only [ZMod.natCast_zmod_val] at hcast
          simp [rows,hcast]
        · have hcast := ZMod.val_injective p h
          simp [rows,hcast]
        · have hcast := congrArg (fun n : ℕ => (n : ZMod p)) h
          simp only [ZMod.natCast_zmod_val] at hcast
          simp [rows,hcast]
      exact Finset.mem_image.mpr ⟨w,Finset.mem_biUnion.mpr
        ⟨w.2,hr,Finset.mem_filter.mpr ⟨hw,rfl⟩⟩,hwcode⟩
    have hrows : rows.card ≤ 3 := by
      have h1 : rows.card ≤ ({z.2, ((z.2.val+1 : ℕ) : ZMod p)} : Finset (ZMod p)).card+1 :=
        Finset.card_insert_le _ _
      have h2 := Finset.card_insert_le z.2 ({((z.2.val+1 : ℕ) : ZMod p)} : Finset (ZMod p))
      simp only [Finset.card_singleton] at h2
      omega
    calc
      S.card ≤ ((rows.biUnion (rowPoints A)).image planeCode).card := Finset.card_le_card hs
      _ ≤ (rows.biUnion (rowPoints A)).card := Finset.card_image_le
      _ ≤ ∑ y ∈ rows, (rowPoints A y).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ rows, C := Finset.sum_le_sum (fun y _hy => hC y)
      _ = rows.card * C := by simp
      _ ≤ 3*C := Nat.mul_le_mul_right C hrows
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

end Encoding
end JSP000617
