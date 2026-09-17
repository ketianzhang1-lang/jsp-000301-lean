import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace JSP000749
open Finset

/-- Elementary finite product estimate; this is the union bound in multiplicative form. -/
lemma one_sub_sum_le_product {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := h0 a (by simp)
    have ha1 := h1 a (by simp)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (by simp [hi])
    have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (by simp [hi])
    have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hs0
    have hmul := mul_le_mul_of_nonneg_left (ih hs0 hs1) (sub_nonneg.mpr ha1)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg ha0 hsum]

lemma twice_sum_range (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (i : ℝ)) = (n : ℝ) * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- Drawing n distinct points from n^2 points costs less than a factor two
compared to drawing ordered points with replacement. -/
lemma desc_factorial_lower (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 2) ^ n ≤ 2 * (n ^ 2).descFactorial n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hsmall (i : ℕ) (hi : i ∈ Finset.range n) : i ≤ n ^ 2 :=
    (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hnn
  have hp := one_sub_sum_le_product (Finset.range n) (fun i => (i : ℝ) / (n : ℝ) ^ 2)
    (fun i _ => by positivity)
    (fun i hi => (div_le_one ha).mpr (by exact_mod_cast hsmall i hi))
  have hs : (∑ i ∈ Finset.range n, (i : ℝ) / (n : ℝ) ^ 2) ≤ 1 / 2 := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ ha).mpr
    have := twice_sum_range n
    nlinarith
  have hid : (∏ i ∈ Finset.range n, (1 - (i : ℝ) / (n : ℝ) ^ 2)) =
      ((n ^ 2).descFactorial n : ℝ) / ((n : ℝ) ^ 2) ^ n := by
    simp_rw [one_sub_div ha.ne']
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_range]
    congr 1
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (hsmall i hi), Nat.cast_pow]
  rw [hid] at hp
  have hp' : (1 : ℝ) / 2 ≤ ((n ^ 2).descFactorial n : ℝ) / ((n : ℝ) ^ 2) ^ n := by linarith
  have h := (le_div_iff₀ (pow_pos ha n)).mp hp'
  have hc : (((n ^ 2) ^ n : ℕ) : ℝ) ≤ 2 * ((n ^ 2).descFactorial n : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hc

/-- The majority colour class contains at least a 2^(-n-1) fraction of all n-sets. -/
theorem binomial_ratio_bound (n : ℕ) (hn : 2 ≤ n) :
    (2 * n ^ 2).choose n ≤ 2 ^ (n + 1) * (n ^ 2).choose n := by
  have h := desc_factorial_lower n hn
  have hd : (2 * n ^ 2).descFactorial n ≤
      2 ^ (n + 1) * (n ^ 2).descFactorial n := by
    calc
      _ ≤ (2 * n ^ 2) ^ n := Nat.descFactorial_le_pow _ _
      _ = 2 ^ n * (n ^ 2) ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (2 * (n ^ 2).descFactorial n) := Nat.mul_le_mul_left _ h
      _ = _ := by rw [pow_succ]; ring
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hd
  exact Nat.le_of_mul_le_mul_left (by simpa only [mul_left_comm] using hd) (Nat.factorial_pos n)

/-- A purely numerical bound needed by the finite tuple-counting argument. -/
theorem tuple_count_bound (E D a N : ℕ) (hE : 0 < E) (hDE : D ≤ E)
    (ha : 0 < a) (hN : 0 < N) (hED : E ≤ a * D) :
    2 ^ N * (E - D) ^ (N * a) < E ^ (N * a) := by
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hDr : (D : ℝ) ≤ E := by exact_mod_cast hDE
  have hEDr : (E : ℝ) ≤ a * D := by exact_mod_cast hED
  let q : ℝ := 1 - (D : ℝ) / E
  have hq0 : 0 ≤ q := by dsimp [q]; exact sub_nonneg.mpr ((div_le_one hEr).mpr hDr)
  have hqa : q ^ a ≤ Real.exp (-1) := by
    calc
      _ ≤ (Real.exp (-((D : ℝ) / E))) ^ a :=
        pow_le_pow_left₀ hq0 (Real.one_sub_le_exp_neg _) _
      _ = Real.exp ((a : ℝ) * (-((D : ℝ) / E))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        have hd : (1 : ℝ) ≤ (a : ℝ) * D / E := (le_div_iff₀ hEr).mpr (by simpa using hEDr)
        rw [mul_neg, ← mul_div_assoc]
        linarith
  have hlt : 2 * q ^ a < 1 := by
    have hx : 2 * Real.exp (-1) < 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (div_lt_one (Real.exp_pos 1)).mpr (by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)])
    linarith
  have hp : (2 * q ^ a) ^ N < 1 := by
    exact pow_lt_one₀ (by positivity) hlt hN.ne'
  have heq : (2 * q ^ a) ^ N =
      (2 : ℝ) ^ N * ((E - D : ℕ) : ℝ) ^ (N * a) / (E : ℝ) ^ (N * a) := by
    dsimp [q]
    rw [Nat.cast_sub hDE, one_sub_div hEr.ne', mul_pow, ← pow_mul,
      Nat.mul_comm a N, div_pow, mul_div_assoc]
  rw [heq] at hp
  have := (div_lt_one (pow_pos hEr _)).mp hp
  exact_mod_cast this

end JSP000749
