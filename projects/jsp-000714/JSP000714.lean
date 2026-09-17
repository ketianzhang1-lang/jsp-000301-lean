/-
Copyright 2026. Released under the Apache License, Version 2.0.
An independent formalization of the classical Erdos--Turan Sidon construction.
Prepared with OpenAI ChatGPT assistance. This is not the full solution of
JSP-000714 / Erdos 861, nor a new mathematical result.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace JSP000714
open Finset

/-- Equal two-term sums have equal unordered pairs; repeated summands are allowed. -/
def Sidon (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Positive translate of the classical modular parabola construction. -/
def point (p i : ℕ) : ℕ := 2 * p * i + i ^ 2 % p + 1

def construction (p : ℕ) : Finset ℕ := (range p).image (point p)

theorem point_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (point p) := by
  intro i j hij
  have hi := Nat.mod_lt (i^2) hp
  have hj := Nat.mod_lt (j^2) hp
  dsimp [point] at hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : 2*p*(i+1) ≤ 2*p*j := Nat.mul_le_mul_left _ h
    simp only [mul_add, mul_one] at this
    omega
  · have : 2*p*(j+1) ≤ 2*p*i := Nat.mul_le_mul_left _ h
    simp only [mul_add, mul_one] at this
    omega

theorem sum_indices {p a b c d : ℕ} (hp : 0 < p)
    (heq : point p a + point p b = point p c + point p d) :
    a+b=c+d := by
  have ha := Nat.mod_lt (a^2) hp
  have hb := Nat.mod_lt (b^2) hp
  have hc := Nat.mod_lt (c^2) hp
  have hd := Nat.mod_lt (d^2) hp
  dsimp [point] at heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : 2*p*(a+b+1) ≤ 2*p*(c+d) := Nat.mul_le_mul_left _ h
    simp only [mul_add, mul_one] at this
    omega
  · have : 2*p*(c+d+1) ≤ 2*p*(a+b) := Nat.mul_le_mul_left _ h
    simp only [mul_add, mul_one] at this
    omega

theorem sum_pair_unique {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    {a b c d : ℕ} (ha : a < p) (_hb : b < p) (hc : c < p) (hd : d < p)
    (heq : point p a + point p b = point p c + point p d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs := sum_indices hp.pos heq
  have hzsum : (a : ZMod p) + b = c + d := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod p)) hs
  have hzsq : (a : ZMod p)^2 + (b : ZMod p)^2 = (c : ZMod p)^2 + (d : ZMod p)^2 := by
    have hz := congrArg (fun n : ℕ => (n : ZMod p)) heq
    simp [point, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hz
    linear_combination hz
  have hprod : (2 : ZMod p) * ((a : ZMod p)-c) * ((a : ZMod p)-d) = 0 := by
    linear_combination hzsq + ((a : ZMod p) - b - c - d) * hzsum
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 2) hdiv
    omega
  have hor : (a : ZMod p) = c ∨ (a : ZMod p) = d := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left htwo))
    · exact Or.inr (sub_eq_zero.mp h)
  have cast_inj (x y : ℕ) (hx : x < p) (hy : y < p)
      (h : (x : ZMod p) = y) : x=y := by
    have hval := congrArg ZMod.val h
    simpa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hval
  rcases hor with h | h
  · have := cast_inj a c ha hc h
    exact Or.inl ⟨this, by omega⟩
  · have := cast_inj a d ha hd h
    exact Or.inr ⟨this, by omega⟩

theorem construction_sidon {p : ℕ} (hp : p.Prime) (hodd : 2 < p) :
    Sidon (construction p) := by
  intro a ha b hb c hc d hd heq
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hc
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hd
  rcases sum_pair_unique hp hodd (mem_range.mp hi) (mem_range.mp hj)
    (mem_range.mp hk) (mem_range.mp hl) heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩

theorem construction_card {p : ℕ} (hp : 0 < p) : (construction p).card = p := by
  rw [construction, card_image_of_injective _ (point_injective hp), card_range]

theorem construction_subset {p : ℕ} (hp : 0 < p) :
    construction p ⊆ Icc 1 (2*p^2) := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  have hi := mem_range.mp hi
  have hr := Nat.mod_lt (i^2) hp
  have hm : 2*p*(i+1) ≤ 2*p*p := Nat.mul_le_mul_left _ hi
  simp only [mem_Icc, point]
  constructor
  · omega
  · nlinarith

theorem sidon_mono {S T : Finset ℕ} (hS : Sidon S) (hT : T ⊆ S) : Sidon T := by
  intro a ha b hb c hc d hd
  exact hS a (hT ha) b (hT hb) c (hT hc) d (hT hd)

noncomputable def sidonFamily (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Icc 1 N).powerset.filter Sidon

theorem powerset_subset_family {N : ℕ} {S : Finset ℕ}
    (hS : Sidon S) (hsub : S ⊆ Icc 1 N) : S.powerset ⊆ sidonFamily N := by
  classical
  intro T hT
  have hTS := mem_powerset.mp hT
  exact mem_filter.mpr ⟨mem_powerset.mpr (hTS.trans hsub), sidon_mono hS hTS⟩

/-- An explicit lower bound for every odd prime, not a finite numerical experiment. -/
theorem prime_count_lower {p : ℕ} (hp : p.Prime) (hodd : 2 < p) :
    2^p ≤ (sidonFamily (2*p^2)).card := by
  have h := card_le_card (powerset_subset_family (construction_sidon hp hodd)
    (construction_subset hp.pos))
  simpa [card_powerset, construction_card hp.pos] using h

theorem family_mono {M N : ℕ} (hMN : M ≤ N) : sidonFamily M ⊆ sidonFamily N := by
  classical
  intro S hS
  obtain ⟨hsub, hs⟩ := mem_filter.mp hS
  refine mem_filter.mpr ⟨mem_powerset.mpr ?_, hs⟩
  intro x hx
  have := mem_Icc.mp (mem_powerset.mp hsub hx)
  exact mem_Icc.mpr ⟨this.1, this.2.trans hMN⟩

/-- A uniform all-parameter exponential lower bound, using Bertrand's postulate. -/
theorem uniform_count_lower {n : ℕ} (hn : 2 ≤ n) :
    2^n ≤ (sidonFamily (8*n^2)).card := by
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hbound : 2*p^2 ≤ 8*n^2 := by nlinarith [sq_nonneg (2*(n:ℤ)-(p:ℤ))]
  calc
    2^n ≤ 2^p := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (sidonFamily (2*p^2)).card := prime_count_lower hp (by omega)
    _ ≤ (sidonFamily (8*n^2)).card := card_le_card (family_mono hbound)

/-- Explicit bound at every sufficiently large integer cutoff. -/
theorem all_cutoffs_lower {N : ℕ} (hN : 32 ≤ N) :
    2 ^ Nat.sqrt (N / 8) ≤ (sidonFamily N).card := by
  have hn : 2 ≤ Nat.sqrt (N / 8) := Nat.le_sqrt'.mpr (by omega)
  have hs := Nat.sqrt_le' (N / 8)
  have hd := Nat.div_mul_le_self N 8
  have hbound : 8 * (Nat.sqrt (N / 8))^2 ≤ N := by omega
  exact (uniform_count_lower hn).trans (card_le_card (family_mono hbound))

end JSP000714
