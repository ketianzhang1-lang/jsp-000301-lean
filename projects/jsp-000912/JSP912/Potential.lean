import JSP912.Decay

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
  ring

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
