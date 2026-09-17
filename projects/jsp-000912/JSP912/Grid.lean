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
