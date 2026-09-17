import JSP912.Construction

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
