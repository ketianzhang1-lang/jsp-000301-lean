import JSP000391

noncomputable section
namespace JSP000391

/-- Scientific-notation normalization with the exact logarithmic exponent. -/
def normalized (g : ℕ) (w : ℝ) : ℝ := w / (g : ℝ) ^ ⌊Real.logb (g : ℝ) w⌋

lemma normalized_bounds (g : ℕ) (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    1 ≤ normalized g w ∧ normalized g w < g := by
  have hg1 : 1 < g := by omega
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hzpos : 0 < (g : ℝ) ^ Int.log g w := zpow_pos hgpos _
  rw [normalized, Real.floor_logb_natCast hw.le]
  constructor
  · apply (le_div_iff₀ hzpos).mpr
    simpa using Int.zpow_log_le_self hg1 hw
  · apply (div_lt_iff₀ hzpos).mpr
    have hu := Int.lt_zpow_succ_log_self (R := ℝ) hg1 w
    simpa only [zpow_add₀ hgpos.ne', zpow_one, mul_comm] using hu

/-- Evaluation of the successive base-g digit words, including the leading digit. -/
def accumulated (g : ℕ) (t : ℝ) : ℕ → ℤ
  | 0 => digit g t 0
  | n + 1 => (g : ℤ) * accumulated g t n + digit g t (n + 1)

lemma accumulated_eq_prefix (g : ℕ) (t : ℝ) (n : ℕ) :
    accumulated g t n = digitPrefix g t n := by
  induction n with
  | zero => simp [accumulated, digit, digitPrefix]
  | succ n ih => simp [accumulated, ih, digit]

/-- The usual rigorous truncation estimate for the decoded digit words. -/
theorem reconstruction_error (g : ℕ) (t : ℝ) (hg : 2 ≤ g) (n : ℕ) :
    0 ≤ t - (accumulated g t n : ℝ) / (g : ℝ) ^ n ∧
    t - (accumulated g t n : ℝ) / (g : ℝ) ^ n < 1 / (g : ℝ) ^ n := by
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hp : 0 < (g : ℝ) ^ n := pow_pos hgpos n
  rw [accumulated_eq_prefix]
  dsimp [digitPrefix]
  have hlo := Int.floor_le (t * (g : ℝ) ^ n)
  have hhi := Int.lt_floor_add_one (t * (g : ℝ) ^ n)
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hlo)
  · apply (sub_lt_iff_lt_add).mpr
    rw [← add_div]
    exact (lt_div_iff₀ hp).mpr (by linarith)

lemma index_lt_radix_pow (g : ℕ) (hg : 2 ≤ g) (n : ℕ) : n < g ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    nlinarith

/-- The digit words converge to the normalized real, not just to an unspecified number. -/
theorem reconstruction_converges (g : ℕ) (t : ℝ) (hg : 2 ≤ g) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |t - (accumulated g t n : ℝ) / (g : ℝ) ^ n| < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, ?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hp : 0 < (g : ℝ) ^ n := pow_pos hgpos n
  have hlarge : (n : ℝ) < (g : ℝ) ^ n := by exact_mod_cast index_lt_radix_pow g hg n
  have hinv : 1 / (g : ℝ) ^ n < δ := by
    apply (div_lt_iff₀ hp).mpr
    have h := (div_lt_iff₀ hδ).mp (hN.trans_le (hnR.trans hlarge.le))
    nlinarith
  obtain ⟨hlo, hhi⟩ := reconstruction_error g t hg n
  rw [abs_of_nonneg hlo]
  exact hhi.trans hinv

/-- Full all-positive-real, all-radix, all-admissible-shift form of Stoll 2005,
Theorem 1.3. Includes actual digit bounds and convergence of their decoded prefixes. -/
theorem stoll_general_base (g : ℕ) (w e : ℝ) (hg : 2 ≤ g) (hw : 0 < w)
    (he0 : -1 / (g : ℝ) ≤ e)
    (he1 : e < ((g : ℝ) + 1) * (g - 2) / g) :
    (∀ n : ℕ,
      sequence g (normalized g w) e (2 * n + 2) -
        (g : ℤ) * sequence g (normalized g w) e (2 * n) =
          digit g (normalized g w) n) ∧
    (∀ n : ℕ, 0 ≤ digit g (normalized g w) n ∧ digit g (normalized g w) n < (g : ℤ)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |normalized g w - (accumulated g (normalized g w) n : ℝ) / (g : ℝ) ^ n| < δ) := by
  obtain ⟨ht0, ht1⟩ := normalized_bounds g w hg hw
  exact ⟨recurrence_extracts_digits g (normalized g w) e hg ht0 ht1 he0 he1,
    digit_bounds g (normalized g w) hg ht0 ht1,
    reconstruction_converges g (normalized g w) hg⟩

/-- There really is an admissible shift for every radix, so the construction
is not vacuous. -/
theorem admissible_shift (g : ℕ) (hg : 2 ≤ g) :
    -1 / (g : ℝ) < ((g : ℝ) + 1) * (g - 2) / g := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < g by linarith)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (g : ℝ) + 1 by linarith) (show 0 ≤ (g : ℝ) - 2 by linarith)]

/-- A constructive answer to the open-ended JSP question: one explicit shift
works for every positive real and hence, in particular, every positive algebraic real. -/
theorem jsp000391 (g : ℕ) (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    ∀ n : ℕ,
      sequence g (normalized g w) (-1 / (g : ℝ)) (2 * n + 2) -
        (g : ℤ) * sequence g (normalized g w) (-1 / (g : ℝ)) (2 * n) =
          digit g (normalized g w) n :=
  (stoll_general_base g w (-1 / (g : ℝ)) hg hw le_rfl (admissible_shift g hg)).1

end JSP000391
