import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Finset

namespace JSP000780General
open Finset

def Full (r n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

lemma full_pow (r a : ℕ) : Full r (a ^ r) := by
  intro p hp hd
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) r

lemma Full.mul {r a b : ℕ} (ha : Full r a) (hb : Full r b) : Full r (a*b) := by
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (ha p hp h) b
  · exact dvd_mul_of_dvd_right (hb p hp h) a

lemma Full.pow {r a : ℕ} (ha : Full r a) (k : ℕ) : Full r (a^k) := by
  induction k with
  | zero =>
    intro p hp hd
    exact False.elim (hp.not_dvd_one (by simpa using hd))
  | succ k ih => simpa [pow_succ] using ih.mul ha

lemma full_coefficient {r c B j : ℕ} (hj : 0 < j)
    (hc : ∀ p, p.Prime → p ∣ c → p ∣ B) : Full r (c * (B^r)^j) := by
  intro p hp hd
  have hpB : p ∣ B := by
    rcases hp.dvd_mul.mp hd with h | h
    · exact hc p hp h
    · exact hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)
  apply dvd_mul_of_dvd_right
  exact (pow_dvd_pow_of_dvd hpB r).trans
    (dvd_pow_self _ (Nat.ne_of_gt hj))

/-- Coefficients need only have prime support inside B; no prime parameter is needed. -/
lemma monomial_full {r c B q j : ℕ} (hj : 0 < j)
    (hc : ∀ p, p.Prime → p ∣ c → p ∣ B) :
    Full r (c * (q^r)^(r-j) * (B^r)^j) := by
  have h := (full_coefficient hj hc).mul ((full_pow r q).pow (r-j))
  convert h using 1; ring

lemma coefficient_support_factorial {K c p : ℕ} (hc : 0 < c) (hcK : c ≤ K)
    (_hp : p.Prime) (hpc : p ∣ c) : p ∣ K.factorial := by
  exact hpc.trans (Nat.dvd_factorial hc hcK)

lemma choose_le_two_pow (r j : ℕ) : r.choose j ≤ 2^r := by
  by_cases hj : j ≤ r
  · rw [← Nat.sum_range_choose]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

lemma choose_three_large (r : ℕ) (hr : 6 ≤ r) :
    r * (r-1) ≤ 2 * r.choose 3 := by
  have h : r.choose 2 ≤ r.choose 3 := Nat.choose_le_succ_of_lt_half_left (by omega)
  have he : 2 * r.choose 2 = r * (r-1) := by
    have e := Nat.descFactorial_eq_factorial_mul_choose r 2
    simpa [Nat.descFactorial_succ, Nat.factorial, mul_comm] using e.symm
  omega

/-- The parity-separated binomial identity, for every exponent. -/
lemma binomial_odd (r : ℕ) (x y : ℤ) :
    (x-y)^r + ∑ j ∈ (Finset.range (r+1)).filter Odd,
      (2 * (r.choose j : ℤ)) * x^(r-j) * y^j = (x+y)^r := by
  rw [show x-y = -y+x by ring, add_pow, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, show x+y = y+x by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : Odd j
  · simp only [ite_eq_left h, h.neg_pow]
    ring
  · have he : Even j := Nat.not_odd_iff_even.mp h
    simp only [ite_eq_right h, he.neg_pow, add_zero]

lemma binomial_odd_nat (r x y : ℕ) (hxy : y ≤ x) :
    (x-y)^r + ∑ j ∈ (Finset.range (r+1)).filter Odd,
      2 * r.choose j * x^(r-j) * y^j = (x+y)^r := by
  have h := binomial_odd r (x : ℤ) (y : ℤ)
  exact_mod_cast h

def splitCount (r : ℕ) : ℕ := r / 2 - 2

def smallCoeffs (r : ℕ) : Finset ℕ := Finset.Ico 1 (splitCount r)

def finalCoeff (r : ℕ) : ℕ := 2 * r.choose 3 - ∑ c ∈ smallCoeffs r, c

def splitCoeffs (r : ℕ) : Finset ℕ := insert (finalCoeff r) (smallCoeffs r)

lemma splitCount_pos (r : ℕ) (hr : 6 ≤ r) : 0 < splitCount r := by
  unfold splitCount; omega

lemma smallCoeffs_card (r : ℕ) : (smallCoeffs r).card = splitCount r - 1 := by
  simp [smallCoeffs]

lemma finalCoeff_large (r : ℕ) (hr : 6 ≤ r) : splitCount r < finalCoeff r := by
  have hm : splitCount r ≤ r - 3 := by unfold splitCount; omega
  have hr1 : r-1+1=r := by omega
  have hb := choose_three_large r hr
  have hs : (∑ c ∈ smallCoeffs r, c) ≤ splitCount r * (splitCount r - 1) := by
    calc
      _ ≤ ∑ _c ∈ smallCoeffs r, splitCount r := by
        apply Finset.sum_le_sum
        intro c hc
        exact (Finset.mem_Ico.mp hc).2.le
      _ = _ := by simp [smallCoeffs_card, mul_comm]
  have hmpos := splitCount_pos r hr
  have hms : splitCount r - 1 + 1 = splitCount r := by omega
  have hm2 : splitCount r + 2 ≤ r := by unfold splitCount; omega
  have hp := Nat.mul_le_mul hm2 (show splitCount r + 1 ≤ r-1 by omega)
  have hsum : (∑ c ∈ smallCoeffs r, c) + splitCount r < 2 * r.choose 3 := by
    nlinarith
  unfold finalCoeff
  omega

lemma splitCoeffs_card (r : ℕ) (hr : 6 ≤ r) : (splitCoeffs r).card = splitCount r := by
  have h := finalCoeff_large r hr
  have hm := splitCount_pos r hr
  rw [splitCoeffs, Finset.card_insert_of_notMem, smallCoeffs_card]
  · omega
  · simp only [smallCoeffs, Finset.mem_Ico]
    omega

lemma splitCoeffs_sum (r : ℕ) (hr : 6 ≤ r) :
    (∑ c ∈ splitCoeffs r, c) = 2 * r.choose 3 := by
  have h := finalCoeff_large r hr
  have hh : finalCoeff r ∉ smallCoeffs r := by
    simp only [smallCoeffs, Finset.mem_Ico]; omega
  rw [splitCoeffs, Finset.sum_insert hh]
  have hd : (∑ c ∈ smallCoeffs r, c) ≤ 2 * r.choose 3 := by
    unfold finalCoeff at h; omega
  exact Nat.sub_add_cancel hd

lemma splitCoeffs_bounds (r c : ℕ) (hr : 6 ≤ r) (hc : c ∈ splitCoeffs r) :
    0 < c ∧ c ≤ 2 * r.choose 3 := by
  have h := finalCoeff_large r hr
  rcases Finset.mem_insert.mp hc with he | he
  · subst c
    exact ⟨by omega, Nat.sub_le _ _⟩
  · have hi := Finset.mem_Ico.mp he
    have hle : finalCoeff r ≤ 2 * r.choose 3 := Nat.sub_le _ _
    omega

lemma odds_card (r : ℕ) : ((Finset.range (r+1)).filter Odd).card = (r+1)/2 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [show r.succ+1 = (r+1)+1 by omega, Finset.range_add_one, Finset.filter_insert]
    by_cases ho : Odd (r+1)
    · rw [ite_eq_left ho, Finset.card_insert_of_notMem, ih]
      · have hm := Nat.odd_iff.mp ho; omega
      · simp
    · rw [ite_eq_right ho, ih]
      have hm : (r+1)%2 ≠ 1 := by simpa only [Nat.odd_iff] using ho
      omega

end JSP000780General
