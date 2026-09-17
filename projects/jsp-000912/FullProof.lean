/-
Complete full-main-scope formalization of JSP-000912 / Erdos Problem 1099.
Prepared on 2026-09-17 with AI assistance for Ketian Zhang.
Mathematical existence theorem: Michael D. Vose (1984).

This implementation was developed independently before the later comparison
with plby/lean-proofs. A pre-existing full formalization was then found there.
NO first-formalization priority or award eligibility is asserted.

Ported to Lean 4.34.0; Mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
See PORT.md for the original Lean 4.19 source and exact compatibility changes.
No project-specific .olean input is needed to check this standalone file.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace JSP912

/-- Denominator baseline for the finite mixed-radix grid. -/
def baseProd (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => baseProd m r * (m ^ (r + 1)) ^ (2 * m)

/-- Integer containing every numerator/denominator choice of the grid. -/
def gridProd (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => gridProd m r * (m ^ (r + 1) * (m ^ (r + 1) + 1)) ^ (2 * m)

lemma baseProd_pos {m : ℕ} (hm : 0 < m) (r : ℕ) : 0 < baseProd m r := by
  induction r with
  | zero => simp [baseProd]
  | succ r ih => exact Nat.mul_pos ih (pow_pos (pow_pos hm _) _)

lemma gridProd_pos {m : ℕ} (hm : 0 < m) (r : ℕ) : 0 < gridProd m r := by
  induction r with
  | zero => simp [gridProd]
  | succ r ih =>
    exact Nat.mul_pos ih (pow_pos (Nat.mul_pos (pow_pos hm _) (by omega)) _)

lemma baseProd_eq (m r : ℕ) : baseProd m r = m ^ (m * r * (r + 1)) := by
  induction r with
  | zero => simp [baseProd]
  | succ r ih =>
    rw [baseProd, ih, ← pow_mul, ← pow_add]
    congr 1
    ring

lemma radix_step {m : ℕ} (hm : 2 ≤ m) (r : ℕ) :
    1 + 1 / (m : ℝ) ^ r ≤ (1 + 1 / (m : ℝ) ^ (r + 1)) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have heq : (m : ℝ) * (1 / (m : ℝ) ^ (r + 1)) = 1 / (m : ℝ) ^ r := by
    rw [pow_succ]
    field_simp
  have hn : (0 : ℝ) ≤ 1 / (m : ℝ) ^ (r + 1) := by positivity
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (m : ℝ) ^ (r + 1) by linarith) m
  simpa only [heq] using h

lemma bounded_power_bracket {z ρ : ℝ} {M : ℕ}
    (hz : 1 ≤ z) (hρ : 1 < ρ) (hzM : z < ρ ^ M) :
    ∃ k : ℕ, k < M ∧ ρ ^ k ≤ z ∧ z < ρ ^ (k + 1) := by
  obtain ⟨k, hk, hks⟩ := exists_nat_pow_near hz hρ
  refine ⟨k, ?_, hk, hks⟩
  by_contra hn
  have hMk : M ≤ k := by omega
  have hh : ρ ^ M ≤ ρ ^ k := by gcongr; linarith
  linarith

/-- All exponents and all real targets in the entire unit octave are covered. -/
theorem grid_approx (m r : ℕ) (hm : 2 ≤ m) (y : ℝ)
    (hy1 : 1 ≤ y) (hy2 : y < 2) :
    ∃ p : ℕ, 0 < p ∧ p ∣ gridProd m r ∧
      (p : ℝ) ≤ (baseProd m r : ℝ) * y ∧
      (baseProd m r : ℝ) * y < (1 + 1 / (m : ℝ) ^ r) * p := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  induction r with
  | zero =>
    refine ⟨1, by omega, by simp [gridProd], ?_, ?_⟩
    · simpa [baseProd] using hy1
    · norm_num [baseProd]
      exact hy2
  | succ r ih =>
    obtain ⟨p, hp0, hpdiv, hplo, hphi⟩ := ih
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    let a : ℕ := m ^ (r + 1)
    let ρ : ℝ := 1 + 1 / (m : ℝ) ^ (r + 1)
    let z : ℝ := (baseProd m r : ℝ) * y / p
    have ha0 : 0 < a := pow_pos hm0 _
    have haR : (0 : ℝ) < a := by exact_mod_cast ha0
    have hρ : 1 < ρ := by
      dsimp [ρ]
      have hh : (0 : ℝ) < 1 / (m : ℝ) ^ (r + 1) := by positivity
      linarith
    have hz : 1 ≤ z := (le_div_iff₀ hpR).2 (by simpa using hplo)
    have hzprev : z < 1 + 1 / (m : ℝ) ^ r :=
      (div_lt_iff₀ hpR).2 hphi
    have hzM : z < ρ ^ m := lt_of_lt_of_le hzprev (radix_step hm r)
    obtain ⟨k, hkm, hklo, hkhi⟩ := bounded_power_bracket hz hρ hzM
    have hkM : k ≤ 2 * m := by omega
    let q : ℕ := p * (a ^ (2 * m - k) * (a + 1) ^ k)
    have hq0 : 0 < q :=
      Nat.mul_pos hp0 (Nat.mul_pos (pow_pos ha0 _) (pow_pos (by omega) _))
    have hpart : a ^ (2 * m - k) * (a + 1) ^ k ∣ (a * (a + 1)) ^ (2 * m) := by
      rw [mul_pow]
      exact mul_dvd_mul (pow_dvd_pow a (Nat.sub_le _ _)) (pow_dvd_pow (a + 1) hkM)
    have hqdiv : q ∣ gridProd m (r + 1) := by
      exact mul_dvd_mul hpdiv hpart
    have hrhoe : ρ = ((a : ℝ) + 1) / a := by
      dsimp [ρ, a]
      push_cast
      field_simp
    have hqeq : (q : ℝ) = (p : ℝ) * (a : ℝ) ^ (2 * m) * ρ ^ k := by
      dsimp [q]
      push_cast
      rw [hrhoe, div_pow]
      have hexp : 2 * m - k + k = 2 * m := Nat.sub_add_cancel hkM
      have hh : (a : ℝ) ^ (2 * m) = (a : ℝ) ^ (2 * m - k) * (a : ℝ) ^ k := by
        rw [← pow_add, hexp]
      rw [hh]
      field_simp
    have hscale : (p : ℝ) * (a : ℝ) ^ (2 * m) * z =
        (baseProd m (r + 1) : ℝ) * y := by
      change (p : ℝ) * (a : ℝ) ^ (2 * m) * ((baseProd m r : ℝ) * y / p) =
        ((baseProd m r * a ^ (2 * m) : ℕ) : ℝ) * y
      push_cast
      field_simp
    have hH : (0 : ℝ) < (p : ℝ) * (a : ℝ) ^ (2 * m) := by positivity
    refine ⟨q, hq0, hqdiv, ?_, ?_⟩
    · rw [hqeq, ← hscale]
      exact mul_le_mul_of_nonneg_left hklo hH.le
    · change (baseProd m (r + 1) : ℝ) * y < ρ * (q : ℝ)
      rw [← hscale, hqeq]
      have hh := mul_lt_mul_of_pos_left hkhi hH
      rw [pow_succ] at hh
      nlinarith


/-- A power-of-two translate of the grid covers the indicated entire interval. -/
theorem grid_scaled (m r E n : ℕ) (hm : 2 ≤ m)
    (hdiv : 2 ^ E * gridProd m r ∣ n) (x : ℝ)
    (hxA : (baseProd m r : ℝ) ≤ x) (hxE : x ≤ (2 : ℝ) ^ E) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ (d : ℝ) ≤ x ∧
      x < (1 + 1 / (m : ℝ) ^ r) * d := by
  have hA0 : 0 < baseProd m r := baseProd_pos (by omega) r
  have hAR : (0 : ℝ) < baseProd m r := by exact_mod_cast hA0
  have hA1 : (1 : ℝ) ≤ baseProd m r := by exact_mod_cast hA0
  have hx0 : 0 < x := lt_of_lt_of_le hAR hxA
  have hz1 : 1 ≤ x / (baseProd m r : ℝ) := (le_div_iff₀ hAR).2 (by simpa using hxA)
  obtain ⟨q, hqlo, hqhi⟩ := exists_nat_pow_near hz1 (show (1 : ℝ) < 2 by norm_num)
  have hqp : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hzle : x / (baseProd m r : ℝ) ≤ x := by
    apply (div_le_iff₀ hAR).2
    nlinarith
  have hqE : q ≤ E := by
    by_contra h
    have hEq : E < q := by omega
    have hh : (2 : ℝ) ^ E < (2 : ℝ) ^ q := by gcongr; norm_num
    linarith
  let y : ℝ := (x / (baseProd m r : ℝ)) / (2 : ℝ) ^ q
  have hy1 : 1 ≤ y := (le_div_iff₀ hqp).2 (by simpa using hqlo)
  have hy2 : y < 2 := by
    apply (div_lt_iff₀ hqp).2
    rw [pow_succ] at hqhi
    linarith
  obtain ⟨p, hp0, hpdiv, hplo, hphi⟩ := grid_approx m r hm y hy1 hy2
  refine ⟨2 ^ q * p, Nat.mul_pos (by positivity) hp0, ?_, ?_, ?_⟩
  · exact dvd_trans (mul_dvd_mul (pow_dvd_pow 2 hqE) hpdiv) hdiv
  · have hs : (2 : ℝ) ^ q * ((baseProd m r : ℝ) * y) = x := by
      dsimp [y]
      field_simp
    push_cast
    rw [← hs]
    exact mul_le_mul_of_nonneg_left hplo hqp.le
  · have hs : (2 : ℝ) ^ q * ((baseProd m r : ℝ) * y) = x := by
      dsimp [y]
      field_simp
    have hh := mul_lt_mul_of_pos_left hphi hqp
    rw [hs] at hh
    push_cast
    nlinarith

/-- Actual consecutive positive divisors, with no omitted intermediate divisor. -/
def Consecutive (n a b : ℕ) : Prop :=
  0 < a ∧ a < b ∧ a ∣ n ∧ b ∣ n ∧
    ∀ d : ℕ, d ∣ n → a < d → d < b → False

lemma Consecutive.b_pos {n a b : ℕ} (h : Consecutive n a b) : 0 < b :=
  lt_trans h.1 h.2.1

/-- The auxiliary grid controls every actual adjacent pair, not merely grid points. -/
theorem grid_consecutive_gap (m r E n a b : ℕ) (hm : 2 ≤ m)
    (hdiv : 2 ^ E * gridProd m r ∣ n) (hab : Consecutive n a b)
    (haA : (baseProd m r : ℝ) ≤ a) (hbE : (b : ℝ) ≤ (2 : ℝ) ^ E) :
    (b : ℝ) / a - 1 ≤ 1 / (m : ℝ) ^ r := by
  have haR : (0 : ℝ) < a := by exact_mod_cast hab.1
  have heps : (0 : ℝ) < 1 / (m : ℝ) ^ r := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  by_contra hn
  have hbad : (1 + 1 / (m : ℝ) ^ r) * a < (b : ℝ) := by
    apply (lt_div_iff₀ haR).1
    linarith
  let x : ℝ := ((b : ℝ) + (1 + 1 / (m : ℝ) ^ r) * a) / 2
  have hxa : (1 + 1 / (m : ℝ) ^ r) * a < x := by dsimp [x]; linarith
  have hxb : x < (b : ℝ) := by dsimp [x]; linarith
  have hax : (a : ℝ) < x := by nlinarith
  obtain ⟨d, hd0, hddiv, hdlo, hdhi⟩ :=
    grid_scaled m r E n hm hdiv x (le_trans haA hax.le) (le_trans hxb.le hbE)
  have had : (a : ℝ) < d := by nlinarith
  have hdb : (d : ℝ) < b := lt_of_le_of_lt hdlo hxb
  exact hab.2.2.2.2 d hddiv (by exact_mod_cast had) (by exact_mod_cast hdb)

lemma consecutive_gap_le_one (n a b E : ℕ) (hab : Consecutive n a b)
    (hdiv : 2 ^ E ∣ n) (hbE : (b : ℝ) ≤ (2 : ℝ) ^ E) :
    (b : ℝ) / a - 1 ≤ 1 := by
  have hh := grid_consecutive_gap 2 0 E n a b (by omega)
    (by simpa [gridProd] using hdiv) hab
    (by simpa [baseProd] using (show (1 : ℝ) ≤ a by exact_mod_cast hab.1)) hbE
  norm_num only [pow_zero, div_one] at hh
  exact hh

end JSP912


namespace JSP912

/-- The product of all precision levels up to `K`. -/
def partialProd (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | K + 1 => partialProd r K * gridProd (2 ^ (K + 1)) r

/-- A deliberately generous, explicit exponent for the binary anchor. -/
def anchorExponent (r K : ℕ) : ℕ := 16 * r * (r + 1) * (K + 1) * 2 ^ K

def candidate (r K : ℕ) : ℕ := 2 ^ anchorExponent r K * partialProd r K

def scaleConstant (r : ℕ) : ℕ := 16 * r * (r + 1) + 2

lemma two_pow_pos (i : ℕ) : 0 < (2 : ℕ) ^ i := by positivity

lemma one_le_two_pow (i : ℕ) : 1 ≤ (2 : ℕ) ^ i := two_pow_pos i

lemma succ_le_two_pow (i : ℕ) : i + 1 ≤ (2 : ℕ) ^ i := by
  induction i with
  | zero => norm_num
  | succ i ih => rw [pow_succ]; omega

lemma le_two_pow (i : ℕ) : i ≤ (2 : ℕ) ^ i := by
  have h := succ_le_two_pow i
  omega

lemma gridProd_dyadic_bound (i r : ℕ) :
    gridProd (2 ^ i) r ≤ 2 ^ (2 * 2 ^ i * (i * r * (r + 1) + r)) := by
  induction r with
  | zero => simp [gridProd]
  | succ r ih =>
    let u : ℕ := i * (r + 1)
    have ha1 : 1 ≤ (2 : ℕ) ^ u := one_le_two_pow u
    have hb : (2 : ℕ) ^ u * (2 ^ u + 1) ≤ 2 ^ (u * 2 + 1) := by
      calc
        (2 : ℕ) ^ u * (2 ^ u + 1) ≤ 2 ^ u * (2 * 2 ^ u) := by nlinarith
        _ = 2 ^ (u * 2 + 1) := by rw [pow_add, pow_mul]; norm_num; ring
    calc
      gridProd (2 ^ i) (r + 1) = gridProd (2 ^ i) r *
          (2 ^ u * (2 ^ u + 1)) ^ (2 * 2 ^ i) := by
            simp only [gridProd, ← pow_mul, u]
      _ ≤ 2 ^ (2 * 2 ^ i * (i * r * (r + 1) + r)) *
          (2 ^ (u * 2 + 1)) ^ (2 * 2 ^ i) :=
            Nat.mul_le_mul ih (Nat.pow_le_pow_left hb _)
      _ = 2 ^ (2 * 2 ^ i * (i * (r + 1) * (r + 1 + 1) + (r + 1))) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            dsimp [u]
            ring

lemma gridProd_dyadic_bound_simple (i r : ℕ) (hi : 1 ≤ i) :
    gridProd (2 ^ i) r ≤ 2 ^ (4 * i * 2 ^ i * r * (r + 1)) := by
  apply le_trans (gridProd_dyadic_bound i r)
  apply Nat.pow_le_pow_right (by omega)
  have hh : r ≤ i * r * (r + 1) := by
    have h1 : r ≤ i * r := by nlinarith
    have h2 : i * r ≤ i * r * (r + 1) := by nlinarith
    omega
  nlinarith [Nat.mul_le_mul_left (2 * 2 ^ i) hh]

lemma partialProd_pos (r K : ℕ) : 0 < partialProd r K := by
  induction K with
  | zero => simp [partialProd]
  | succ K ih => exact Nat.mul_pos ih (gridProd_pos (two_pow_pos _) r)

lemma partialProd_bound (r K : ℕ) : partialProd r K ≤ 2 ^ anchorExponent r K := by
  induction K with
  | zero => simpa [partialProd] using (one_le_two_pow (anchorExponent r 0))
  | succ K ih =>
    calc
      partialProd r (K + 1) = partialProd r K * gridProd (2 ^ (K + 1)) r := rfl
      _ ≤ 2 ^ anchorExponent r K * 2 ^ (4 * (K + 1) * 2 ^ (K + 1) * r * (r + 1)) :=
        Nat.mul_le_mul ih (gridProd_dyadic_bound_simple (K + 1) r (by omega))
      _ = 2 ^ (anchorExponent r K + 4 * (K + 1) * 2 ^ (K + 1) * r * (r + 1)) :=
        (pow_add _ _ _).symm
      _ ≤ 2 ^ anchorExponent r (K + 1) := by
        apply Nat.pow_le_pow_right (by omega)
        simp only [anchorExponent, pow_succ]
        ring_nf
        omega

lemma level_dvd_partialProd (r i K : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K) :
    gridProd (2 ^ i) r ∣ partialProd r K := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases he : i = K + 1
    · subst i
      exact dvd_mul_left _ _
    · have hik : i ≤ K := by omega
      exact dvd_mul_of_dvd_left (ih hik) _

lemma anchor_dvd (r K : ℕ) : 2 ^ anchorExponent r K ∣ candidate r K := by
  exact dvd_mul_right _ _

lemma level_with_anchor_dvd (r i K : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K) :
    2 ^ anchorExponent r K * gridProd (2 ^ i) r ∣ candidate r K := by
  exact mul_dvd_mul_left _ (level_dvd_partialProd r i K hi hiK)

lemma candidate_pos (r K : ℕ) : 0 < candidate r K :=
  Nat.mul_pos (two_pow_pos _) (partialProd_pos r K)

lemma index_le_anchorExponent (r K : ℕ) (hr : 1 ≤ r) : K ≤ anchorExponent r K := by
  have hc : 1 ≤ 16 * r * (r + 1) := by nlinarith
  have hp := one_le_two_pow K
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_right (K + 1) hc) hp
  dsimp [anchorExponent]
  nlinarith

lemma index_le_candidate (r K : ℕ) (hr : 1 ≤ r) : K ≤ candidate r K := by
  calc
    K ≤ 2 ^ K := le_two_pow K
    _ ≤ 2 ^ anchorExponent r K := Nat.pow_le_pow_right (by omega) (index_le_anchorExponent r K hr)
    _ ≤ candidate r K := by
      have hh : 1 ≤ partialProd r K := partialProd_pos r K
      dsimp [candidate]
      nlinarith [two_pow_pos (anchorExponent r K)]

lemma baseProd_dyadic_eq (i r : ℕ) :
    baseProd (2 ^ i) r = 2 ^ (r * (r + 1) * i * 2 ^ i) := by
  rw [baseProd_eq, ← pow_mul]
  congr 1
  ring

lemma anchorExponent_le_scale (r K : ℕ) :
    1 + anchorExponent r K ≤ scaleConstant r * 4 ^ K := by
  have hh := succ_le_two_pow K
  have h4 : (4 : ℕ) ^ K = 2 ^ K * 2 ^ K := by
    rw [← mul_pow]
    norm_num
  have hp := one_le_two_pow K
  dsimp [anchorExponent, scaleConstant]
  rw [h4]
  have hmul := Nat.mul_le_mul_right (16 * r * (r + 1) * 2 ^ K) hh
  nlinarith [Nat.mul_le_mul hp hp]

lemma dyadic_level_gap (r K i a b : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K)
    (hab : Consecutive (candidate r K) a b)
    (haA : ((2 : ℝ) ^ (r * (r + 1) * i * 2 ^ i)) ≤ a)
    (hbE : (b : ℝ) ≤ (2 : ℝ) ^ anchorExponent r K) :
    (b : ℝ) / a - 1 ≤ 1 / (2 : ℝ) ^ (r * i) := by
  have hm : 2 ≤ (2 : ℕ) ^ i := by
    have hh := Nat.pow_le_pow_right (show (1 : ℕ) ≤ 2 by omega) hi
    simpa using hh
  have hh := grid_consecutive_gap (2 ^ i) r (anchorExponent r K) (candidate r K) a b hm
    (level_with_anchor_dvd r i K hi hiK) hab
    (by simpa only [baseProd_dyadic_eq, Nat.cast_pow, Nat.cast_ofNat] using haA) hbE
  simpa only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm i r] using hh

end JSP912


namespace JSP912

lemma log_two_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma inverse_power_rpow_le (r i : ℕ) (β : ℝ) (hr : 4 ≤ (r : ℝ) * β) :
    (1 / (2 : ℝ) ^ (r * i)) ^ β ≤ 1 / (2 : ℝ) ^ (4 * i) := by
  have hh : (2 : ℝ) ^ (4 * i) ≤ ((2 : ℝ) ^ (r * i)) ^ β := by
    rw [← Real.rpow_natCast_mul (by norm_num) (r * i) β,
      ← Real.rpow_natCast (2 : ℝ) (4 * i)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hr (show (0 : ℝ) ≤ i by positivity)]
  rw [one_div, Real.inv_rpow (by positivity)]
  simpa only [one_div] using (one_div_le_one_div_of_le (by positivity) hh)

/-- Finite multiscale estimate; no asymptotic or convergence hypothesis is assumed. -/
lemma multiscale_decay (r K : ℕ) (β B g t : ℝ)
    (hβ : 0 < β) (hr : 4 ≤ (r : ℝ) * β)
    (hB : 0 ≤ B) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ht0 : 0 ≤ t)
    (htK : t ≤ B * (4 : ℝ) ^ K)
    (hgrid : ∀ i : ℕ, i < K → B * (4 : ℝ) ^ i < t →
      g ≤ 1 / (2 : ℝ) ^ (r * i)) :
    g ^ β * t ^ 2 ≤ 16 * B ^ 2 := by
  have hgpow0 : 0 ≤ g ^ β := Real.rpow_nonneg hg0 β
  have hgpow1 : g ^ β ≤ 1 := Real.rpow_le_one hg0 hg1 hβ.le
  induction K with
  | zero =>
    simp only [pow_zero, mul_one] at htK
    have hs : t ^ 2 ≤ B ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hgpow1 (sq_nonneg t)
    nlinarith [sq_nonneg B]
  | succ K ih =>
    by_cases ht : t ≤ B * (4 : ℝ) ^ K
    · exact ih ht (fun i hi hh => hgrid i (by omega) hh)
    · have hg := hgrid K (by omega) (lt_of_not_ge ht)
      have hp : g ^ β ≤ 1 / (2 : ℝ) ^ (4 * K) :=
        le_trans (Real.rpow_le_rpow hg0 hg hβ.le) (inverse_power_rpow_le r K β hr)
      have hs : t ^ 2 ≤ (B * (4 : ℝ) ^ (K + 1)) ^ 2 := by gcongr
      have h4 : (2 : ℝ) ^ (4 * K) = ((4 : ℝ) ^ K) ^ 2 := by
        calc
          (2 : ℝ) ^ (4 * K) = (16 : ℝ) ^ K := by rw [pow_mul]; norm_num
          _ = ((4 : ℝ) ^ 2) ^ K := by norm_num
          _ = ((4 : ℝ) ^ K) ^ 2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      have heq : (1 / (2 : ℝ) ^ (4 * K)) * (B * (4 : ℝ) ^ (K + 1)) ^ 2 =
          16 * B ^ 2 := by
        rw [h4, pow_succ]
        field_simp
        ring
      calc
        g ^ β * t ^ 2 ≤ (1 / (2 : ℝ) ^ (4 * K)) * (B * (4 : ℝ) ^ (K + 1)) ^ 2 :=
          mul_le_mul hp hs (sq_nonneg t) (by positivity)
        _ = 16 * B ^ 2 := heq

lemma baselineExponent_le_scale (r i : ℕ) :
    r * (r + 1) * i * 2 ^ i + 2 ≤ scaleConstant r * 4 ^ i := by
  have hi := le_two_pow i
  have hp := one_le_two_pow i
  have h4 : (4 : ℕ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
  dsimp [scaleConstant]
  rw [h4]
  have hh := Nat.mul_le_mul_left (r * (r + 1) * 2 ^ i) hi
  have hp2 := Nat.mul_le_mul hp hp
  ring_nf at hh hp2 ⊢
  omega

lemma threshold_implies_baseline (r i a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hg : (b : ℝ) / a - 1 ≤ 1)
    (ht : (scaleConstant r : ℝ) * (4 : ℝ) ^ i < 1 + Real.log b) :
    (2 : ℝ) ^ (r * (r + 1) * i * 2 ^ i) ≤ a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb2a : (b : ℝ) ≤ 2 * a := by
    apply (div_le_iff₀ haR).1
    linarith
  have hlog := Real.log_le_log hbR hb2a
  rw [Real.log_mul (by norm_num) haR.ne'] at hlog
  have hcoeff : ((r * (r + 1) * i * 2 ^ i : ℕ) : ℝ) + 2 ≤
      (scaleConstant r : ℝ) * (4 : ℝ) ^ i := by
    exact_mod_cast baselineExponent_le_scale r i
  have hpowlog : Real.log ((2 : ℝ) ^ (r * (r + 1) * i * 2 ^ i)) ≤
      ((r * (r + 1) * i * 2 ^ i : ℕ) : ℝ) := by
    rw [Real.log_pow]
    have hn : (0 : ℝ) ≤ (r * (r + 1) * i * 2 ^ i : ℕ) := by positivity
    nlinarith [log_two_le_one]
  apply (Real.log_le_log_iff (by positivity) haR).1
  linarith [log_two_le_one]

/-- Uniform weighted estimate for the lower half covered by the binary anchor. -/
theorem lower_gap_weight (r K a b : ℕ) (β : ℝ) (hβ : 0 < β)
    (hr : 4 ≤ (r : ℝ) * β) (hab : Consecutive (candidate r K) a b)
    (hbE : (b : ℝ) ≤ (2 : ℝ) ^ anchorExponent r K) :
    ((b : ℝ) / a - 1) ^ β * (1 + Real.log b) ^ 2 ≤
      16 * (scaleConstant r : ℝ) ^ 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast hab.1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hab.b_pos
  have hba : (a : ℝ) < b := by exact_mod_cast hab.2.1
  have hgap0 : 0 ≤ (b : ℝ) / a - 1 := by
    have hh : 1 < (b : ℝ) / a := (lt_div_iff₀ haR).2 (by simpa using hba)
    linarith
  have hgap1 := consecutive_gap_le_one (candidate r K) a b (anchorExponent r K) hab
    (anchor_dvd r K) hbE
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hab.b_pos)
  have ht : 1 + Real.log (b : ℝ) ≤ (scaleConstant r : ℝ) * (4 : ℝ) ^ K := by
    have hh := Real.log_le_log hbR hbE
    rw [Real.log_pow] at hh
    have hE : (0 : ℝ) ≤ (anchorExponent r K : ℝ) := by positivity
    have hs : (1 : ℝ) + anchorExponent r K ≤ (scaleConstant r : ℝ) * (4 : ℝ) ^ K := by
      exact_mod_cast anchorExponent_le_scale r K
    nlinarith [log_two_le_one]
  apply multiscale_decay r K β (scaleConstant r : ℝ) ((b : ℝ) / a - 1)
    (1 + Real.log (b : ℝ)) hβ hr (by positivity) hgap0 hgap1 (by linarith) ht
  intro i hi hit
  by_cases hiz : i = 0
  · simpa [hiz] using hgap1
  · have hi1 : 1 ≤ i := by omega
    exact dyadic_level_gap r K i a b hi1 (by omega) hab
      (threshold_implies_baseline r i a b hab.1 hab.b_pos hgap1 hit) hbE

end JSP912


namespace JSP912

noncomputable def potential (x : ℝ) : ℝ := 1 / (1 + Real.log x)

lemma potential_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ potential x := by
  have hlog := Real.log_nonneg hx
  unfold potential
  positivity

lemma potential_le_one {x : ℝ} (hx : 1 ≤ x) : potential x ≤ 1 := by
  have hlog := Real.log_nonneg hx
  unfold potential
  apply (div_le_iff₀ (by linarith : 0 < 1 + Real.log x)).2
  linarith

lemma potential_antitone {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    potential b ≤ potential a := by
  have hla := Real.log_nonneg ha
  have hlab := Real.log_le_log (by linarith : 0 < a) hab
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma gap_le_log_difference {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgap : b / a - 1 ≤ 1) :
    b / a - 1 ≤ 2 * (Real.log b - Real.log a) := by
  have hb : 0 < b := lt_trans ha hab
  have hq : 1 < b / a := (lt_div_iff₀ ha).2 (by simpa using hab)
  have hq0 : 0 < b / a := by positivity
  have hq2 : b / a ≤ 2 := by linarith
  have hl0 : 0 ≤ Real.log (b / a) := Real.log_nonneg hq.le
  have hh := Real.one_sub_inv_le_log_of_pos hq0
  have hh' := mul_le_mul_of_nonneg_left hh hq0.le
  simp only [mul_sub, mul_one, mul_inv_cancel₀ hq0.ne'] at hh'
  have hh2 := mul_le_mul_of_nonneg_right hq2 hl0
  rw [Real.log_div hb.ne' ha.ne'] at hh' hh2
  linarith

/-- A single lower-half gap is charged to a decreasing, bounded potential. -/
lemma real_gap_cost {a b β C : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hgap : b / a - 1 ≤ 1)
    (hweight : (b / a - 1) ^ β * (1 + Real.log b) ^ 2 ≤ C) :
    (b / a - 1) ^ (β + 1) ≤ 2 * C * (potential a - potential b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla := Real.log_nonneg ha
  have hlb := Real.log_nonneg (show 1 ≤ b by linarith)
  have hlogs := Real.log_le_log ha0 hab.le
  have hx : 0 < 1 + Real.log a := by linarith
  have hy : 0 < 1 + Real.log b := by linarith
  have hdelta : 0 ≤ potential a - potential b :=
    sub_nonneg.mpr (potential_antitone ha hab.le)
  have hid : (potential a - potential b) * (1 + Real.log a) * (1 + Real.log b) =
      Real.log b - Real.log a := by
    unfold potential
    field_simp
    ring
  have hmono := mul_le_mul_of_nonneg_left (show 1 + Real.log a ≤ 1 + Real.log b by linarith)
    hdelta
  have hmono' := mul_le_mul_of_nonneg_right hmono hy.le
  have hlog := gap_le_log_difference ha0 hab hgap
  have hcharge : b / a - 1 ≤ 2 * (potential a - potential b) * (1 + Real.log b) ^ 2 := by
    nlinarith [hid]
  have hg : 0 < b / a - 1 := by
    have hh : 1 < b / a := (lt_div_iff₀ ha0).2 (by simpa using hab)
    linarith
  have hp : 0 ≤ (b / a - 1) ^ β := Real.rpow_nonneg hg.le β
  have hcharge' := mul_le_mul_of_nonneg_left hcharge hp
  have hw' := mul_le_mul_of_nonneg_left hweight (show 0 ≤ 2 * (potential a - potential b) by positivity)
  rw [Real.rpow_add hg, Real.rpow_one]
  nlinarith

lemma Consecutive.reflect {n a b : ℕ} (hab : Consecutive n a b) (hn : 0 < n) :
    Consecutive n (n / b) (n / a) := by
  have haD := hab.2.2.1
  have hbD := hab.2.2.2.1
  have haD' := Nat.div_dvd_of_dvd haD
  have hbD' := Nat.div_dvd_of_dvd hbD
  refine ⟨Nat.pos_of_dvd_of_pos hbD' hn,
    (Nat.div_lt_div_left hn.ne' hbD haD).2 hab.2.1, hbD', haD', ?_⟩
  intro d hd had hdb
  have hd' := Nat.div_dvd_of_dvd hd
  have hl : a < n / d := by
    have hh := (Nat.div_lt_div_left hn.ne' haD' hd).2 hdb
    simpa only [Nat.div_div_self haD hn.ne'] using hh
  have hu : n / d < b := by
    have hh := (Nat.div_lt_div_left hn.ne' hd hbD').2 had
    simpa only [Nat.div_div_self hbD hn.ne'] using hh
  exact hab.2.2.2.2 (n / d) hd' hl hu

lemma reflected_ratio {n a b : ℕ} (hn : 0 < n) (hab : Consecutive n a b) :
    ((n / a : ℕ) : ℝ) / (n / b : ℕ) = (b : ℝ) / a := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast hab.1.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hab.b_pos.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_div hab.2.2.1 haR, Nat.cast_div hab.2.2.2.1 hbR]
  field_simp

lemma reflected_below_anchor (r K a b : ℕ)
    (hab : Consecutive (candidate r K) a b)
    (hb : (2 : ℝ) ^ anchorExponent r K < b) :
    ((candidate r K / a : ℕ) : ℝ) ≤ (2 : ℝ) ^ anchorExponent r K := by
  have hbN : 2 ^ anchorExponent r K < b := by exact_mod_cast hb
  have ha : 2 ^ anchorExponent r K ≤ a := by
    by_contra hh
    exact hab.2.2.2.2 (2 ^ anchorExponent r K) (anchor_dvd r K) (by omega) hbN
  have hh : candidate r K ≤ a * 2 ^ anchorExponent r K := by
    exact Nat.mul_le_mul ha (partialProd_bound r K)
  have hdiv : candidate r K / a ≤ 2 ^ anchorExponent r K := Nat.div_le_of_le_mul hh
  exact_mod_cast hdiv

/-- An integer divisor and its complementary divisor define a bounded potential. -/
noncomputable def divisorPotential (n d : ℕ) : ℝ :=
  potential (d : ℝ) - potential ((n / d : ℕ) : ℝ)

lemma divisorPotential_bounds {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    -1 ≤ divisorPotential n d ∧ divisorPotential n d ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_dvd_of_pos hd hn
  have he1 : (1 : ℝ) ≤ (n / d : ℕ) := by
    exact_mod_cast Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd) hn
  have h1 := potential_nonneg hd1
  have h2 := potential_le_one hd1
  have h3 := potential_nonneg he1
  have h4 := potential_le_one he1
  unfold divisorPotential
  constructor <;> linarith

/-- Covers every actual consecutive divisor pair, including those above the anchor. -/
theorem all_gap_cost (r K a b : ℕ) (β : ℝ) (hβ : 0 < β)
    (hr : 4 ≤ (r : ℝ) * β) (hab : Consecutive (candidate r K) a b) :
    ((b : ℝ) / a - 1) ^ (β + 1) ≤
      (32 * (scaleConstant r : ℝ) ^ 2) *
        (divisorPotential (candidate r K) a - divisorPotential (candidate r K) b) := by
  have hn := candidate_pos r K
  have haref := hab.reflect hn
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hab.1
  have he1 : (1 : ℝ) ≤ (candidate r K / b : ℕ) := by exact_mod_cast haref.1
  have habR : (a : ℝ) < b := by exact_mod_cast hab.2.1
  have hrefR : ((candidate r K / b : ℕ) : ℝ) < (candidate r K / a : ℕ) := by
    exact_mod_cast haref.2.1
  have hdown : 0 ≤ potential (a : ℝ) - potential (b : ℝ) :=
    sub_nonneg.mpr (potential_antitone ha1 habR.le)
  have hup : 0 ≤ potential ((candidate r K / b : ℕ) : ℝ) -
      potential ((candidate r K / a : ℕ) : ℝ) :=
    sub_nonneg.mpr (potential_antitone he1 hrefR.le)
  by_cases hbE : (b : ℝ) ≤ (2 : ℝ) ^ anchorExponent r K
  · have hw := lower_gap_weight r K a b β hβ hr hab hbE
    have hg := consecutive_gap_le_one (candidate r K) a b (anchorExponent r K) hab
      (anchor_dvd r K) hbE
    have hc := real_gap_cost ha1 habR hg hw
    unfold divisorPotential
    nlinarith [mul_nonneg (sq_nonneg (scaleConstant r : ℝ)) hup]
  · have hrefE := reflected_below_anchor r K a b hab (lt_of_not_ge hbE)
    have hw := lower_gap_weight r K (candidate r K / b) (candidate r K / a) β hβ hr haref hrefE
    have hg := consecutive_gap_le_one (candidate r K) (candidate r K / b) (candidate r K / a)
      (anchorExponent r K) haref (anchor_dvd r K) hrefE
    have hc := real_gap_cost he1 hrefR hg hw
    rw [reflected_ratio hn hab] at hc
    unfold divisorPotential
    nlinarith [mul_nonneg (sq_nonneg (scaleConstant r : ℝ)) hdown]

end JSP912


namespace JSP912

/-- All positive divisors, in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ := (Nat.divisors n).sort (· ≤ ·)

/-- The sum over every consecutive pair in the complete ordered divisor list. -/
noncomputable def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).map (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum

lemma mem_sortedDivisors {n d : ℕ} (hn : 0 < n) :
    d ∈ sortedDivisors n ↔ d ∣ n := by
  simp [sortedDivisors, Nat.mem_divisors, hn.ne']

lemma sortedDivisors_strict (n : ℕ) : (sortedDivisors n).Pairwise (· < ·) :=
  (Nat.divisors n).sortedLT_sort.pairwise

lemma sortedDivisors_get_le (n i j : ℕ)
    (hi : i < (sortedDivisors n).length) (hj : j < (sortedDivisors n).length)
    (hij : i ≤ j) : (sortedDivisors n)[i] ≤ (sortedDivisors n)[j] := by
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst j
    rfl
  · exact (List.pairwise_iff_getElem.mp (sortedDivisors_strict n) i j hi hj hlt).le

lemma sortedDivisors_neighbors (n i : ℕ) (hn : 0 < n)
    (hi : i + 1 < (sortedDivisors n).length) :
    Consecutive n (sortedDivisors n)[i] (sortedDivisors n)[i + 1] := by
  have hi0 : i < (sortedDivisors n).length := by omega
  have haD : (sortedDivisors n)[i] ∣ n :=
    (mem_sortedDivisors hn).mp (List.getElem_mem hi0)
  have hbD : (sortedDivisors n)[i + 1] ∣ n :=
    (mem_sortedDivisors hn).mp (List.getElem_mem hi)
  have hab := List.pairwise_iff_getElem.mp (sortedDivisors_strict n) i (i + 1) hi0 hi (by omega)
  refine ⟨Nat.pos_of_dvd_of_pos haD hn, hab, haD, hbD, ?_⟩
  intro d hd had hdb
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp ((mem_sortedDivisors hn).mpr hd)
  by_cases hji : j ≤ i
  · have hh := sortedDivisors_get_le n j i hj hi0 hji
    rw [hjeq] at hh
    omega
  · have hh := sortedDivisors_get_le n (i + 1) j hi hj (by omega)
    rw [hjeq] at hh
    omega

lemma sortedDivisors_zip_consecutive {n a b : ℕ} (hn : 0 < n)
    (hp : (a, b) ∈ (sortedDivisors n).zip (sortedDivisors n).tail) :
    Consecutive n a b := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp
  have hil : i + 1 < (sortedDivisors n).length := by
    simp only [List.length_zip, List.length_tail] at hi
    omega
  have hae := congrArg Prod.fst heq
  have hbe := congrArg Prod.snd heq
  simp only [List.getElem_zip, List.getElem_tail] at hae hbe
  have hh := sortedDivisors_neighbors n i hn hil
  rw [hae, hbe] at hh
  exact hh

lemma potential_sum_telescope (Φ : ℕ → ℝ) (C : ℝ) (a : ℕ) (l : List ℕ) :
    (((a :: l).zip l).map (fun p => C * (Φ p.1 - Φ p.2))).sum =
      C * (Φ a - Φ ((a :: l).getLast (by simp))) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.getLast_cons_cons]
    rw [ih b]
    ring

lemma potential_sum_le (Φ : ℕ → ℝ) (C : ℝ) (l : List ℕ) (hC : 0 ≤ C)
    (hbounds : ∀ d ∈ l, -1 ≤ Φ d ∧ Φ d ≤ 1) :
    ((l.zip l.tail).map (fun p => C * (Φ p.1 - Φ p.2))).sum ≤ 2 * C := by
  cases l with
  | nil => simp; positivity
  | cons a l =>
    simp only [List.tail_cons]
    rw [potential_sum_telescope]
    have ha := hbounds a (by simp)
    have hb := hbounds ((a :: l).getLast (by simp)) (List.getLast_mem (by simp))
    have hd : Φ a - Φ ((a :: l).getLast (by simp)) ≤ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hd hC]

/-- Explicit full-scope bound, uniform in the unbounded construction parameter K. -/
theorem hAlpha_candidate_bound (α : ℝ) (r K : ℕ) (hα : 1 < α)
    (hr : 4 ≤ (r : ℝ) * (α - 1)) :
    hAlpha α (candidate r K) ≤ 64 * (scaleConstant r : ℝ) ^ 2 := by
  have hn := candidate_pos r K
  have hcost : ∀ p ∈ (sortedDivisors (candidate r K)).zip (sortedDivisors (candidate r K)).tail,
      ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α ≤
        (32 * (scaleConstant r : ℝ) ^ 2) *
          (divisorPotential (candidate r K) p.1 - divisorPotential (candidate r K) p.2) := by
    intro p hp
    have hh := all_gap_cost r K p.1 p.2 (α - 1) (by linarith) hr
      (sortedDivisors_zip_consecutive hn hp)
    simpa only [sub_add_cancel] using hh
  have hs := List.sum_le_sum hcost
  have ht := potential_sum_le (divisorPotential (candidate r K))
    (32 * (scaleConstant r : ℝ) ^ 2) (sortedDivisors (candidate r K)) (by positivity)
    (fun d hd => divisorPotential_bounds hn ((mem_sortedDivisors hn).mp hd))
  unfold hAlpha
  linarith

/-- Full affirmative answer to JSP-000912 / Erdős 1099, for every real α > 1.
    The witness n is strictly positive and exceeds any prescribed cutoff. -/
theorem jsp_000912_full :
    ∀ α : ℝ, 1 < α → ∃ C : ℝ, 0 < C ∧
      ∀ M : ℕ, ∃ n : ℕ, 0 < n ∧ M ≤ n ∧ hAlpha α n ≤ C := by
  intro α hα
  have hβ : 0 < α - 1 := by linarith
  obtain ⟨r, hr⟩ := exists_nat_ge (4 / (α - 1))
  have hrprod : 4 ≤ (r : ℝ) * (α - 1) := (div_le_iff₀ hβ).mp hr
  have hrpos : 0 < (r : ℝ) := by nlinarith
  have hr1 : 1 ≤ r := by exact_mod_cast hrpos
  have hB : (0 : ℝ) < scaleConstant r := by
    unfold scaleConstant
    positivity
  refine ⟨64 * (scaleConstant r : ℝ) ^ 2, by positivity, ?_⟩
  intro M
  exact ⟨candidate r M, candidate_pos r M, index_le_candidate r M hr1,
    hAlpha_candidate_bound α r M hα hrprod⟩

/-- Exact conventional quantifier form, without additional witness conditions. -/
theorem erdos_1099 :
    ∀ α : ℝ, 1 < α → ∃ C : ℝ, ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ hAlpha α n ≤ C := by
  intro α hα
  obtain ⟨C, _, hC⟩ := jsp_000912_full α hα
  refine ⟨C, ?_⟩
  intro M
  obtain ⟨n, _, hn, hbound⟩ := hC M
  exact ⟨n, hn, hbound⟩

end JSP912
