import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-!
Quantitative Pell construction for JSP-000303 / Erdos 367.
Mathematical construction: Wouter van Doorn and Terence Tao.
Independent Lean implementation, prepared with OpenAI ChatGPT assistance.
This proves a known lower-bound component, not the open n^(2+o(1)) upper bound.
-/

namespace JSP000303
open scoped BigOperators

def xy : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 => (3 * (xy j).1 + 8 * (xy j).2, (xy j).1 + 3 * (xy j).2)

def X (j : ℕ) := (xy j).1
def Y (j : ℕ) := (xy j).2

@[simp] lemma X_zero : X 0 = 1 := rfl
@[simp] lemma Y_zero : Y 0 = 0 := rfl
@[simp] lemma X_succ (j : ℕ) : X (j+1) = 3*X j+8*Y j := rfl
@[simp] lemma Y_succ (j : ℕ) : Y (j+1) = X j+3*Y j := rfl

lemma pell (j : ℕ) : X j ^ 2 = 8 * Y j ^ 2 + 1 := by
  induction j with
  | zero => norm_num
  | succ j ih => simp only [X_succ, Y_succ]; nlinarith

lemma X_pos (j : ℕ) : 0 < X j := by
  have := pell j
  nlinarith

lemma Y_strictMono : StrictMono Y := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [Y_succ]
  have := X_pos j
  omega

lemma growth (j : ℕ) : X j + Y j ≤ 11 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    simp only [X_succ, Y_succ, pow_succ]
    omega

def alpha : Zsqrtd 8 := ⟨3, 1⟩

lemma alpha_pow (j : ℕ) : alpha ^ j = ⟨(X j : ℤ), (Y j : ℤ)⟩ := by
  induction j with
  | zero => ext <;> simp
  | succ j ih =>
    rw [pow_succ, ih]
    ext <;> simp [alpha, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- A fifth-power lifting identity in any commutative ring. -/
lemma lift_five {R : Type*} [CommRing R] (z a : R)
    (h : 5*a ∣ z+1) : 25*a ∣ z^5+1 := by
  obtain ⟨w, hw⟩ := h
  have hz : z = 5*a*w-1 := by linear_combination hw
  refine ⟨w-10*a*w^2+50*a^2*w^3-125*a^3*w^4+125*a^4*w^5, ?_⟩
  rw [hz]
  ring

lemma alpha_congruence (t : ℕ) :
    (5 : Zsqrtd 8)^(t+1) ∣ alpha^(3*5^t)+1 := by
  induction t with
  | zero =>
    refine ⟨⟨20,7⟩, ?_⟩
    ext <;> norm_num [alpha, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  | succ t ih =>
    have h := lift_five (alpha^(3*5^t)) ((5 : Zsqrtd 8)^t) (by
      simpa [pow_succ, mul_comm] using ih)
    convert h using 1 <;> ring

def index : ℕ → ℕ
  | 0 => 1
  | t+1 => 5*index t+2

lemma index_eq (t : ℕ) : 2*index t+1 = 3*5^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [index, pow_succ]; omega

lemma index_pos (t : ℕ) : 0 < index t := by
  cases t <;> simp [index]

def witness (t : ℕ) : ℕ := 8 * Y (index t)^2

lemma witness_pos (t : ℕ) : 0 < witness t := by
  have hy := Y_strictMono (index_pos t)
  simp only [Y_zero] at hy
  unfold witness
  positivity

lemma prime_power_divides (t : ℕ) : 5^(t+1) ∣ witness t+2 := by
  obtain ⟨w, hw⟩ := alpha_congruence t
  rw [← index_eq t, show 2*index t+1 = index t*2+1 by omega,
    pow_succ, pow_mul, alpha_pow] at hw
  have h5 (k : ℕ) : (5 : Zsqrtd 8)^k = ⟨(5:ℤ)^k, 0⟩ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, ih]; ext <;> simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [h5] at hw
  have hr := congrArg Zsqrtd.re hw
  have hi := congrArg Zsqrtd.im hw
  simp [alpha, Zsqrtd.re_mul, Zsqrtd.im_mul, pow_two] at hr hi
  have hp : (X (index t):ℤ)^2 = 8*(Y (index t):ℤ)^2+1 := by
    exact_mod_cast pell (index t)
  have heq : (2 : ℤ) * ((witness t : ℤ)+2) =
      (5:ℤ)^(t+1)*(3*w.re-8*w.im) := by
    dsimp [witness]
    linear_combination 3*hr-8*hi-hp
  have hd : (5:ℤ)^(t+1) ∣ 2*((witness t:ℤ)+2) := ⟨_,heq⟩
  have hn : 5^(t+1) ∣ 2*(witness t+2) := by exact_mod_cast hd
  exact (Nat.Coprime.pow_left (t+1) (by decide : Nat.Coprime 5 2)).dvd_of_dvd_mul_left hn

/-- The exact prime-factorization definition in Formal Conjectures, Erdos 367. -/
def B (r n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support with r ≤ n.factorization p, p^n.factorization p

def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

lemma B_eq_self {n : ℕ} (hn : n ≠ 0) (h : Powerful n) : B 2 n = n := by
  have hf : n.factorization.support.filter (fun p => 2 ≤ n.factorization p) =
      n.factorization.support := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdiv : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    exact (hprime.pow_dvd_iff_le_factorization hn).mp (h p hprime hdiv)
  rw [B, hf]
  exact Nat.prod_factorization_pow_eq_self hn

lemma square_powerful (a : ℕ) : Powerful (a^2) := by
  intro p hp h
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h) 2

lemma eight_mul_square_powerful (a : ℕ) : Powerful (8*a^2) := by
  intro p hp h
  rcases hp.dvd_mul.mp h with h8 | ha
  · have hp2 : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp (by norm_num)
        (show p ∣ 2^3 by simpa using h8)
    subst p
    exact dvd_mul_of_dvd_left (by norm_num : 2^2 ∣ 8) _
  · exact dvd_mul_of_dvd_right (square_powerful a p hp ha) _

lemma prime_power_le_B {n p k : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hk : 2 ≤ k) (hd : p^k ∣ n) : p^k ≤ B 2 n := by
  have hkv := (hp.pow_dvd_iff_le_factorization hn).mp hd
  have hv : 2 ≤ n.factorization p := hk.trans hkv
  have hm : p ∈ n.factorization.support.filter (fun q => 2 ≤ n.factorization q) := by
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), hv⟩
  have hdB : p^k ∣ B 2 n :=
    (pow_dvd_pow p hkv).trans (Finset.dvd_prod_of_mem (fun q => q^n.factorization q) hm)
  have hpos : 0 < B 2 n := by
    apply Finset.prod_pos
    intro q hq
    exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _
  exact Nat.le_of_dvd hpos hdB

lemma quantitative_nat (t : ℕ) (ht : 1 ≤ t) :
    witness t * (witness t+1) * 5^(t+1) ≤
      B 2 (witness t) * B 2 (witness t+1) * B 2 (witness t+2) := by
  have hn := witness_pos t
  have h0 := B_eq_self hn.ne' (eight_mul_square_powerful (Y (index t)))
  have h1 : B 2 (witness t+1) = witness t+1 := by
    apply B_eq_self (by omega)
    rw [show witness t+1 = X (index t)^2 from (pell (index t)).symm]
    exact square_powerful _
  rw [h0, h1]
  exact Nat.mul_le_mul_left _ (prime_power_le_B (by omega) (by norm_num : Nat.Prime 5)
    (by omega) (prime_power_divides t))

lemma index_ge (t : ℕ) : t+1 ≤ index t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [index]; omega

lemma witness_gt (t : ℕ) : t < witness t := by
  have hy : index t ≤ Y (index t) := Y_strictMono.id_le _
  have hj := index_ge t
  unfold witness
  nlinarith

lemma log_witness_le (t : ℕ) : Real.log (witness t) ≤ 6*(5:ℝ)^(t+1) := by
  have hn : 0 < (witness t : ℝ) := by exact_mod_cast witness_pos t
  have hy : (Y (index t) : ℝ) ≤ (11:ℝ)^index t := by
    exact_mod_cast (le_trans (Nat.le_add_left _ _) (growth (index t)))
  have hb : (witness t : ℝ) ≤ 8*((11:ℝ)^index t)^2 := by
    dsimp [witness]
    push_cast
    gcongr
  have hl := Real.log_le_log hn hb
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hl
  have h8 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)
  have h11 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<11)
  norm_num at h8 h11
  have hj : 2*(index t:ℝ)+1 = 3*(5:ℝ)^t := by exact_mod_cast index_eq t
  norm_num only [Nat.cast_ofNat] at hl
  have hm : (index t:ℝ)*Real.log 11 ≤ (index t:ℝ)*10 := by
    exact mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ)≤(index t:ℝ))
  rw [pow_succ]
  linarith

lemma triple_prod (n : ℕ) :
    (∏ m ∈ Finset.Ico n (n+3), B 2 m) = B 2 n * B 2 (n+1) * B 2 (n+2) := by
  have hs : Finset.Ico n (n+3) = {n, n+1, n+2} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hs]
  simp [mul_assoc]

/-- Explicit quantitative bound, with the fixed constant 1/6, at every witness t >= 1. -/
theorem logarithmic_bound (t : ℕ) (ht : 1 ≤ t) :
    (1/6:ℝ) * ((witness t:ℝ)^2 * Real.log (witness t)) ≤
      ((∏ m ∈ Finset.Ico (witness t) (witness t+3), B 2 m : ℕ):ℝ) := by
  rw [triple_prod]
  have hq : (witness t:ℝ)*((witness t:ℝ)+1)*(5:ℝ)^(t+1) ≤
      (B 2 (witness t):ℝ)*(B 2 (witness t+1):ℝ)*(B 2 (witness t+2):ℝ) := by
    exact_mod_cast quantitative_nat t ht
  have hl := mul_le_mul_of_nonneg_left (log_witness_le t) (sq_nonneg (witness t:ℝ))
  push_cast
  nlinarith [show (0:ℝ) ≤ (witness t:ℝ)*(5:ℝ)^(t+1) by positivity]

/-- The complete logarithmic lower-bound variant of Erdos 367. -/
theorem erdos_367_k_three_lower :
    ∃ c > (0:ℝ), ∃ᶠ n : ℕ in Filter.atTop,
      c*((n:ℝ)^2*Real.log (n:ℝ)) ≤
        ((∏ m ∈ Finset.Ico n (n+3), B 2 m : ℕ):ℝ) := by
  refine ⟨1/6, by norm_num, Filter.frequently_atTop.mpr ?_⟩
  intro N
  exact ⟨witness (N+1), by have := witness_gt (N+1); omega,
    logarithmic_bound (N+1) (by omega)⟩

lemma one_le_B (r n : ℕ) : 1 ≤ B r n := by
  apply Finset.one_le_prod
  intro p hp
  exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

lemma product_mono {j k n : ℕ} (hjk : j ≤ k) :
    (∏ m ∈ Finset.Ico n (n+j), B 2 m) ≤ ∏ m ∈ Finset.Ico n (n+k), B 2 m :=
  Finset.prod_le_prod_of_subset_of_one_le (Finset.Ico_subset_Ico_right (by omega))
    (fun m _ _ => one_le_B 2 m)

/-- The same constant works for every fixed interval length at least three. -/
theorem logarithmic_lower_all_k (k : ℕ) (hk : 3 ≤ k) :
    ∃ᶠ n : ℕ in Filter.atTop,
      (1/6:ℝ)*((n:ℝ)^2*Real.log (n:ℝ)) ≤
        ((∏ m ∈ Finset.Ico n (n+k), B 2 m : ℕ):ℝ) := by
  apply Filter.frequently_atTop.mpr
  intro N
  refine ⟨witness (N+1), by have := witness_gt (N+1); omega, ?_⟩
  exact (logarithmic_bound (N+1) (by omega)).trans (by exact_mod_cast product_mono (n := witness (N+1)) hk)

/-- The ratio to n^2 exceeds any given real constant arbitrarily far out. -/
theorem ratio_unbounded (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ C*(n:ℝ)^2 <
      ((∏ m ∈ Finset.Ico n (n+3), B 2 m : ℕ):ℝ) := by
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt C (by norm_num : (1:ℝ)<5)
  let t := N+s+1
  have ht : 1 ≤ t := by omega
  have hN : N ≤ witness t := by have := witness_gt t; omega
  refine ⟨witness t, hN, ?_⟩
  have hc : C < (5:ℝ)^(t+1) := hs.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have hn : 0 < (witness t:ℝ) := by exact_mod_cast witness_pos t
  have hmul := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hn)
  have hq : (witness t:ℝ)*((witness t:ℝ)+1)*(5:ℝ)^(t+1) ≤
      (B 2 (witness t):ℝ)*(B 2 (witness t+1):ℝ)*(B 2 (witness t+2):ℝ) := by
    exact_mod_cast quantitative_nat t ht
  rw [triple_prod]
  push_cast
  nlinarith [show (0:ℝ) ≤ (witness t:ℝ)*(5:ℝ)^(t+1) by positivity]

/-- Every interval length k >= 3 fails the stronger quadratic upper bound,
with eventual quantifiers as required by Big-O. -/
theorem not_quadratic_bound (k : ℕ) (hk : 3 ≤ k) :
    ¬ Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => ((∏ m ∈ Finset.Ico n (n+k), B 2 m : ℕ):ℝ))
      (fun n : ℕ => (n:ℝ)^2) := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hC
  obtain ⟨n, hn, hratio⟩ := ratio_unbounded C N
  have hb := hN n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_sq] at hb
  have hmono : ((∏ m ∈ Finset.Ico n (n+3), B 2 m : ℕ):ℝ) ≤
      ((∏ m ∈ Finset.Ico n (n+k), B 2 m : ℕ):ℝ) := by
    exact_mod_cast product_mono (n := n) hk
  linarith

end JSP000303
