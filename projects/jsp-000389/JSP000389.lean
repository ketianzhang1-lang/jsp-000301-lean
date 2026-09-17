/- Copyright 2026. Released under the Apache-2.0 license. -/
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
JSP-000389 / Erdos 478: elementary all-prime factorial-residue bounds.
This file proves scoped known bounds and obstructions, not the open asymptotic formula.
Prepared with OpenAI ChatGPT assistance. Mathematical background and scope: README.md.
-/

open Finset
namespace JSP000389

def factorialResidues (p : ℕ) : Finset (ZMod p) :=
  (Ico 1 p).image (fun n => (n.factorial : ZMod p))

def Socialist (p : ℕ) : Prop :=
  p.Prime ∧ 5 < p ∧ Set.InjOn (fun n => (n.factorial : ZMod p)) (Set.Ico 2 p)

variable {p : ℕ} [Fact p.Prime]

lemma factorial_ne_zero {n : ℕ} (hn : n < p) : (n.factorial : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  rw [(Fact.out : p.Prime).dvd_factorial]
  omega

lemma cast_inj_below {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = b) : a = b := by
  have := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using this

lemma factorial_step {n : ℕ} (hn : 0 < n) :
    (n.factorial : ZMod p) = (n : ZMod p) * ((n - 1).factorial : ZMod p) := by
  conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.sub_add_cancel hn]

/-- A bound for every prime, with no search cutoff. -/
theorem residue_count_bound : p - 2 ≤ (factorialResidues p).card * ((factorialResidues p).card - 1) := by
  let f : ℕ → ZMod p × ZMod p := fun k => (k.factorial, (k - 1).factorial)
  have hm : Set.MapsTo f (↑(Ico 2 p)) (↑(factorialResidues p).offDiag) := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hk
    apply mem_offDiag.mpr
    refine ⟨mem_image.mpr ⟨k, mem_Ico.mpr ⟨by omega, hhi⟩, rfl⟩,
      mem_image.mpr ⟨k - 1, mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
    change (k.factorial : ZMod p) ≠ ((k - 1).factorial : ZMod p)
    intro he
    rw [factorial_step (by omega : 0 < k)] at he
    have he' : (k : ZMod p) = 1 := (mul_right_cancel₀ (factorial_ne_zero (n := k - 1) (by omega))) (by simpa using he)
    have := cast_inj_below (a := k) (b := 1) hhi (by have := (Fact.out : p.Prime).two_le; omega) (by simpa using he')
    omega
  have hi : Set.InjOn f (↑(Ico 2 p)) := by
    intro a ha b hb hab
    obtain ⟨hal, hah⟩ := mem_Ico.mp ha
    obtain ⟨hbl, hbh⟩ := mem_Ico.mp hb
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    change (a.factorial : ZMod p) = (b.factorial : ZMod p) at h1
    change ((a - 1).factorial : ZMod p) = ((b - 1).factorial : ZMod p) at h2
    rw [factorial_step (by omega : 0 < a), factorial_step (by omega : 0 < b), h2] at h1
    exact cast_inj_below hah hbh (mul_right_cancel₀ (factorial_ne_zero (by omega)) h1)
  have h := card_le_card_of_injOn f hm hi
  simpa only [Nat.card_Ico, offDiag_card, Nat.mul_sub_left_distrib, mul_one] using h

lemma factorial_pred_pred (hp : 2 < p) : ((p - 2).factorial : ZMod p) = 1 := by
  have h := ZMod.wilsons_lemma p
  rw [factorial_step (by omega : 0 < p - 1)] at h
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [hcast, show p - 1 - 1 = p - 2 by omega] at h
  linear_combination -h

/-- A socialist prime must be 1 modulo 4; in particular every prime 3 modulo 4
larger than 5 has a repeated factorial residue in the intended index range. -/
theorem socialist_mod_four (h : Socialist p) : p % 4 = 1 := by
  obtain ⟨hprime, hp, hinj⟩ := h
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have htwo : p % 2 = 1 := Nat.odd_iff.mp hodd
  by_contra hn
  have hthree : p % 4 = 3 := by omega
  have hm : Odd ((p - 1) / 2) := Nat.odd_iff.mpr (by omega)
  have hf := ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq hodd
  rw [ZMod.wilsons_lemma, hm.neg_one_pow] at hf
  have hs : (((p - 1) / 2).factorial : ZMod p) ^ 2 = 1 := by linear_combination hf
  have hcases : (((p - 1) / 2).factorial : ZMod p) = 1 ∨
      (((p - 1) / 2).factorial : ZMod p) = -1 := (sq_eq_one_iff).mp hs
  rcases hcases with hpos | hneg
  · have he := hinj (show (p - 1) / 2 ∈ Set.Ico 2 p by constructor <;> omega)
      (show p - 2 ∈ Set.Ico 2 p by constructor <;> omega)
      (hpos.trans (factorial_pred_pred (by omega)).symm)
    omega
  · have he := hinj (show (p - 1) / 2 ∈ Set.Ico 2 p by constructor <;> omega)
      (show p - 1 ∈ Set.Ico 2 p by constructor <;> omega)
      (hneg.trans (ZMod.wilsons_lemma p).symm)
    omega

lemma factorial_complement {k : ℕ} (hk : k < p) :
    (k.factorial : ZMod p) * ((p - 1 - k).factorial : ZMod p) = (-1) ^ (k + 1) := by
  have h := Nat.factorial_mul_descFactorial (show k ≤ p - 1 by omega)
  have hh : ((p - 1 - k).factorial : ZMod p) *
      ((p - 1).descFactorial k : ZMod p) = ((p - 1).factorial : ZMod p) := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod p)) h
  rw [ZMod.cast_descFactorial (by omega), ZMod.wilsons_lemma] at hh
  have hsq : ((-1 : ZMod p) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; simp
  calc
    (k.factorial : ZMod p) * ((p - 1 - k).factorial : ZMod p) =
        (-1) ^ k * (((p - 1 - k).factorial : ZMod p) * ((-1) ^ k * k.factorial)) := by
      linear_combination - ((k.factorial : ZMod p) * ((p - 1 - k).factorial : ZMod p)) * hsq
    _ = (-1) ^ k * (-1) := by rw [hh]
    _ = (-1) ^ (k + 1) := by rw [pow_succ]

lemma product_split_reflect {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (∏ k ∈ range (2*m+1), f k) = f m * ∏ k ∈ range m, (f k * f (2*m-k)) := by
  have hr := prod_Ico_reflect f 0 (m := m) (n := 2*m) (by omega)
  simp only [Nat.Ico_zero_eq_range, Nat.sub_zero] at hr
  rw [show 2*m+1-m = m+1 by omega] at hr
  rw [← prod_range_mul_prod_Ico f (show m+1 ≤ 2*m+1 by omega),
    prod_range_succ, ← hr, prod_mul_distrib]
  ac_rfl

lemma sign_product (t : ℕ) : (∏ k ∈ range (2*t), (-1 : ZMod p) ^ (k+1)) = (-1)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2*(t+1) = (2*t+1)+1 by omega, prod_range_succ, prod_range_succ, ih]
    have h1 : (-1 : ZMod p) ^ (2*t+1) = -1 := by simp [pow_add, pow_mul]
    have h2 : (-1 : ZMod p) ^ (2*t+1+1) = 1 := by
      rw [show 2*t+1+1 = 2*(t+1) by omega]; simp [pow_mul]
    rw [h1, h2, mul_one, pow_succ]

/-- The product identity used in the classical modulus-eight obstruction. -/
lemma factorial_product (t : ℕ) (hp : p = 4*t+1) :
    (∏ k ∈ range p, (k.factorial : ZMod p)) = (-1)^t * ((2*t).factorial : ZMod p) := by
  have hsplit := product_split_reflect (fun k => (k.factorial : ZMod p)) (2*t)
  rw [show 2*(2*t)+1 = p by omega] at hsplit
  rw [hsplit]
  have hc : (∏ k ∈ range (2*t), (k.factorial : ZMod p) * ((2*(2*t)-k).factorial : ZMod p)) =
      ∏ k ∈ range (2*t), (-1 : ZMod p)^(k+1) := by
    apply prod_congr rfl
    intro k hk
    rw [show 2*(2*t)-k = p-1-k by omega]
    exact factorial_complement (by have := mem_range.mp hk; omega)
  rw [hc, sign_product, mul_comm]

lemma nonzero_residues_eq : (univ : Finset (ZMod p)).erase 0 =
    (Ico 1 p).image (fun n : ℕ => (n : ZMod p)) := by
  ext x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := (mem_erase.mp hx).1
    have hv : 0 < x.val := Nat.pos_of_ne_zero (by simpa using hx0)
    exact mem_image.mpr ⟨x.val, mem_Ico.mpr ⟨hv, x.val_lt⟩, ZMod.natCast_zmod_val x⟩
  · intro hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    obtain ⟨hl, hh⟩ := mem_Ico.mp hn
    apply mem_erase.mpr
    refine ⟨?_, mem_univ _⟩
    intro he
    have := cast_inj_below (a := n) (b := 0) hh (Fact.out : p.Prime).pos (by simpa using he)
    omega

lemma product_nonzero : (∏ x ∈ (univ : Finset (ZMod p)).erase 0, x) = -1 := by
  rw [nonzero_residues_eq, prod_image]
  · exact ZMod.prod_Ico_one_prime p
  · intro a ha b hb he
    exact cast_inj_below (mem_Ico.mp ha).2 (mem_Ico.mp hb).2 he

lemma product_factorials_range (hp : 2 ≤ p) :
    (∏ k ∈ range p, (k.factorial : ZMod p)) = ∏ k ∈ Ico 2 p, (k.factorial : ZMod p) := by
  rw [← prod_range_mul_prod_Ico (fun k => (k.factorial : ZMod p)) hp]
  simp [prod_range_succ]

/-- Exactly one nonzero residue is omitted when 2!,..., (p-1)! are distinct. -/
lemma missing_residue (h : Socialist p) : ∃ r : ZMod p,
    r ≠ 0 ∧ r ∉ (Ico 2 p).image (fun n => (n.factorial : ZMod p)) ∧
    ((univ : Finset (ZMod p)).erase 0) =
      insert r ((Ico 2 p).image (fun n => (n.factorial : ZMod p))) := by
  let S := (Ico 2 p).image (fun n => (n.factorial : ZMod p))
  let U := (univ : Finset (ZMod p)).erase 0
  have hsub : S ⊆ U := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact mem_erase.mpr ⟨factorial_ne_zero (mem_Ico.mp hk).2, mem_univ _⟩
  have hS : S.card = p - 2 := by
    rw [card_image_iff.mpr (by simpa only [coe_Ico] using h.2.2), Nat.card_Ico]
  have hU : U.card = p - 1 := by simp [U, ZMod.card]
  have hcard : (U \ S).card = 1 := by
    have := card_sdiff_add_card_eq_card hsub
    rw [hS, hU] at this
    have := h.2.1
    omega
  obtain ⟨r, hr⟩ := card_eq_one.mp hcard
  have hrU : r ∈ U ∧ r ∉ S := mem_sdiff.mp (by rw [hr]; simp)
  refine ⟨r, (mem_erase.mp hrU.1).1, hrU.2, ?_⟩
  change U = insert r S
  ext x
  constructor
  · intro hx
    by_cases hxS : x ∈ S
    · exact mem_insert_of_mem hxS
    · have hxD : x ∈ U \ S := mem_sdiff.mpr ⟨hx, hxS⟩
      rw [hr] at hxD
      exact mem_insert.mpr (Or.inl (mem_singleton.mp hxD))
  · intro hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hrU.1
    · exact hsub hx

lemma missing_product (h : Socialist p) {r : ZMod p}
    (hr : r ∉ (Ico 2 p).image (fun n => (n.factorial : ZMod p)))
    (hU : (univ : Finset (ZMod p)).erase 0 =
      insert r ((Ico 2 p).image (fun n => (n.factorial : ZMod p)))) :
    r * (∏ k ∈ range p, (k.factorial : ZMod p)) = -1 := by
  have he := product_nonzero (p := p)
  rw [hU, prod_insert hr, prod_image (by simpa only [coe_Ico] using h.2.2),
    ← product_factorials_range (by have := h.2.1; omega)] at he
  exact he

/-- The classical necessary condition: a socialist prime is 5 modulo 8. -/
theorem socialist_mod_eight (h : Socialist p) : p % 8 = 5 := by
  have hfour := socialist_mod_four h
  let t := p / 4
  have hp : p = 4*t+1 := by dsimp [t]; omega
  have hm : (p - 1)/2 = 2*t := by omega
  have ht : 0 < t := by have := h.2.1; omega
  obtain ⟨r, _, hr, hU⟩ := missing_residue h
  have he := missing_product h hr hU
  rw [factorial_product t hp] at he
  have hf := ZMod.half_factorial_sq_eq_neg_one (p := p) (by omega)
  rw [hm] at hf
  have hn : ((2*t).factorial : ZMod p) ≠ 0 := factorial_ne_zero (by omega)
  have hodd : t % 2 = 1 := by
    by_contra hc
    have htEven : Even t := Nat.even_iff.mpr (by omega)
    rw [htEven.neg_one_pow, one_mul, ← hf, pow_two] at he
    have hre := mul_right_cancel₀ hn he
    apply hr
    exact mem_image.mpr ⟨2*t, mem_Ico.mpr ⟨by omega, by omega⟩, hre.symm⟩
  omega

/-- A socialist prime omits exactly the negative half-factorial. -/
theorem socialist_missing_residue (h : Socialist p) :
    (univ : Finset (ZMod p)).erase 0 =
      insert (-(((p-1)/2).factorial : ZMod p))
        ((Ico 2 p).image (fun n => (n.factorial : ZMod p))) := by
  have height := socialist_mod_eight h
  let t := p / 4
  have hp : p = 4*t+1 := by dsimp [t]; omega
  have hm : (p - 1)/2 = 2*t := by omega
  have htodd : Odd t := Nat.odd_iff.mpr (by dsimp [t]; omega)
  obtain ⟨r, _, hr, hU⟩ := missing_residue h
  have he := missing_product h hr hU
  rw [factorial_product t hp, htodd.neg_one_pow] at he
  have hf := ZMod.half_factorial_sq_eq_neg_one (p := p) (by omega)
  rw [hm] at hf
  have hn := factorial_ne_zero (p := p) (n := 2*t) (by omega)
  have hre : r = -((2*t).factorial : ZMod p) := by
    apply mul_right_cancel₀ hn
    linear_combination -he + hf
  rw [hre, ← hm] at hU
  exact hU

/-- The left-factorial necessary condition of Andrejic and Tatarevic. -/
theorem socialist_left_factorial (h : Socialist p) :
    ((∑ k ∈ range p, (k.factorial : ZMod p)) - 2) ^ 2 = -1 := by
  have height := socialist_mod_eight h
  have hp : 5 < p := h.2.1
  have hm : (p-1)/2 < p := by omega
  have hnegnot : -(((p-1)/2).factorial : ZMod p) ∉
      (Ico 2 p).image (fun n => (n.factorial : ZMod p)) := by
    obtain ⟨r, _, hr, hU⟩ := missing_residue h
    have hc := socialist_missing_residue h
    have hcard : ((Ico 2 p).image (fun n => (n.factorial : ZMod p))).card = p-2 := by
      rw [card_image_iff.mpr (by simpa only [coe_Ico] using h.2.2), Nat.card_Ico]
    intro hin
    rw [insert_eq_of_mem hin] at hc
    have he := congrArg Finset.card hc
    simp only [card_erase_of_mem (mem_univ (0 : ZMod p)), card_univ, ZMod.card, hcard] at he
    omega
  have hs : (∑ x : ZMod p, x) = 0 := by
    simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one (ZMod p) 1
      (by rw [ZMod.card]; omega)
  have hu : (∑ x ∈ (univ : Finset (ZMod p)).erase 0, x) = 0 := by
    simpa only [add_zero] using ((sum_erase_add univ (fun x : ZMod p => x) (mem_univ 0)).trans hs)
  rw [socialist_missing_residue h, sum_insert hnegnot,
    sum_image (by simpa only [coe_Ico] using h.2.2)] at hu
  have hsum : (∑ k ∈ range p, (k.factorial : ZMod p)) =
      2 + ∑ k ∈ Ico 2 p, (k.factorial : ZMod p) := by
    rw [← sum_range_add_sum_Ico (fun k => (k.factorial : ZMod p)) (by omega : 2 ≤ p)]
    norm_num [sum_range_succ]
  rw [hsum]
  have he : 2 + ∑ k ∈ Ico 2 p, (k.factorial : ZMod p) - 2 =
      (((p-1)/2).factorial : ZMod p) := by linear_combination hu
  rw [he]
  exact ZMod.half_factorial_sq_eq_neg_one (by omega)

/-- The residue-count definition in natural-number remainder notation. -/
def residueCount (p : ℕ) : ℕ :=
  ((Ico 1 p).image (fun n => n.factorial % p)).card

lemma residueCount_eq : residueCount p = (factorialResidues p).card := by
  have he : (factorialResidues p).image ZMod.val = (Ico 1 p).image (fun n => n.factorial % p) := by
    simp only [factorialResidues, image_image, Function.comp_def, ZMod.val_natCast]
  rw [residueCount, ← he, card_image_of_injective _ (ZMod.val_injective p)]

theorem factorial_residue_lower_bound (p : ℕ) (hp : p.Prime) :
    p - 2 ≤ residueCount p * (residueCount p - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [residueCount_eq]
  exact residue_count_bound

lemma residues_without_one (hp : 3 < p) : factorialResidues p =
    (Ico 2 p).image (fun n => (n.factorial : ZMod p)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    obtain ⟨hl, hh⟩ := mem_Ico.mp hk
    by_cases hk1 : k = 1
    · subst k
      refine mem_image.mpr ⟨p-2, mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa using factorial_pred_pred (p := p) (by omega)
    · exact mem_image.mpr ⟨k, mem_Ico.mpr ⟨by omega, hh⟩, rfl⟩
  · intro hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨k, mem_Ico.mpr ⟨by have := (mem_Ico.mp hk).1; omega,
      (mem_Ico.mp hk).2⟩, rfl⟩

/-- All primes outside the exceptional residue class lose at least two nonzero residues. -/
theorem factorial_residue_upper_bound (p : ℕ) (hprime : p.Prime) (hp : 5 < p)
    (hmod : p % 8 ≠ 5) : residueCount p ≤ p - 3 := by
  let : Fact p.Prime := ⟨hprime⟩
  have hni : ¬ Set.InjOn (fun n => (n.factorial : ZMod p)) (Set.Ico 2 p) := by
    intro hi
    exact hmod (socialist_mod_eight ⟨hprime, hp, hi⟩)
  have hne : ((Ico 2 p).image (fun n => (n.factorial : ZMod p))).card ≠ (Ico 2 p).card := by
    intro he
    exact hni (by simpa only [coe_Ico] using card_image_iff.mp he)
  have hle := card_image_le (s := Ico 2 p) (f := fun n => (n.factorial : ZMod p))
  rw [Nat.card_Ico] at hne hle
  rw [residueCount_eq, residues_without_one (by omega)]
  omega

/-- The two principal necessary conditions, quantified over all natural p. -/
theorem socialist_necessary_conditions (p : ℕ) (h : Socialist p) :
    p % 8 = 5 ∧ ((∑ k ∈ range p, (k.factorial : ZMod p)) - 2)^2 = -1 := by
  let : Fact p.Prime := ⟨h.1⟩
  exact ⟨socialist_mod_eight h, socialist_left_factorial h⟩

end JSP000389
