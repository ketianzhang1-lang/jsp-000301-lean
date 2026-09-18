import JSP000250
import ErdosProblems.Erdos294.SharpLower

/-! We retain our prime-obstruction upper proof and connect it to the
attributed Liu--Sawhney lower-bound development. The exact model equivalence
and least-exception identity include N = 0. UPSTREAM.json and PROVENANCE.md
record the imported source closure and distinguish it from our additions. -/

open Filter

namespace JSP000250

theorem representable_iff_upstream (N t : ℕ) :
    Representable N t ↔ Erdos294.Represents N t := by
  simp only [Representable, Erdos294.Represents, UnitFractions.rec_sum,
    Nat.succ_le_iff]

theorem representable_iff_increasing_sequence (N t : ℕ) :
    Representable N t ↔ Erdos294.SequenceRepresents N t := by
  rw [Erdos294.sequenceRepresents_iff_represents, representable_iff_upstream]

theorem firstException_eq_firstForbidden (N : ℕ) :
    firstException N = Erdos294.firstForbidden N := by
  apply Nat.le_antisymm
  · apply firstException_le (Erdos294.firstForbidden_pos N)
    rw [representable_iff_upstream]
    exact Erdos294.not_represents_firstForbidden N
  · by_contra h
    have hr := Erdos294.represents_of_pos_of_lt_firstForbidden
      (Nat.succ_le_iff.mpr (firstException_spec N).1) (Nat.lt_of_not_ge h)
    exact (firstException_spec N).2 ((representable_iff_upstream N _).mpr hr)

/-- The literal lower comparison profile, with the triple-logarithm exponent 20. -/
noncomputable def lowerProfile (N : ℕ) : ℝ :=
  (N : ℝ) / (Real.log (N : ℝ) * (Real.log (Real.log (N : ℝ))) ^ 3 *
    (Real.log (Real.log (Real.log (N : ℝ)))) ^ 20)

theorem lowerProfile_eq_upstream (N : ℕ) :
    lowerProfile N = Erdos294.lowerProfile 20 N := rfl

/-- All positive least denominators in the explicit lower range are realized. -/
theorem eventually_all_small_denominators_representable :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, 0 < t →
      (t : ℝ) ≤ (1 / 1000000 : ℝ) * lowerProfile N → Representable N t := by
  filter_upwards [Erdos294.SharpLower.eventually_represents_of_three_le_of_le_profile,
    eventually_ge_atTop (6 : ℕ)] with N hrep hN
  intro t ht hbound
  rw [representable_iff_upstream]
  by_cases hthree : 3 ≤ t
  · apply hrep t hthree
    have hc : Erdos294.SharpLower.lowerConstant = (1 / 1000000 : ℝ) := by
      norm_num [Erdos294.SharpLower.lowerConstant]
    simpa only [hc, Erdos294.SharpOuterScales.outerExponent,
      lowerProfile, Erdos294.lowerProfile] using hbound
  · have hcases : t = 1 ∨ t = 2 := by omega
    rcases hcases with rfl | rfl
    · exact Erdos294.SharpLower.represents_one (by omega)
    · exact Erdos294.SharpLower.represents_two hN

/-- Our exact increasing-sequence interface for all denominators in the lower range. -/
theorem eventually_all_small_denominators_sequences :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, 0 < t →
      (t : ℝ) ≤ (1 / 1000000 : ℝ) * lowerProfile N →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ), StrictMono n ∧ n 0 = t ∧
        (∀ i, n i ≤ N) ∧ ∑ i, (1 : ℚ) / n i = 1 := by
  filter_upwards [eventually_all_small_denominators_representable] with N hN
  intro t ht hbound
  exact ((representable_iff_increasing_sequence N t).mp (hN t ht hbound)).2

theorem eventually_strict_lower_bound :
    ∀ᶠ N : ℕ in atTop,
      (1 / 1000000 : ℝ) * lowerProfile N < firstException N := by
  filter_upwards [eventually_all_small_denominators_representable] with N hN
  by_contra h
  exact (firstException_spec N).2
    (hN (firstException N) (firstException_spec N).1 (le_of_not_gt h))

/-- The upper direction uses our original prime-obstruction proof. -/
theorem eventually_explicit_upper_bound :
    ∀ᶠ N : ℕ in atTop,
      (firstException N : ℝ) ≤ 128 * N / Real.log (N : ℝ) := by
  have hlog : ∀ᶠ N : ℕ in atTop, 128 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 128)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with N hl hn
  exact firstException_upper_bound N (by omega) hl

/-- The complete two-sided Liu--Sawhney estimate, with explicit constants. -/
theorem jsp_000250 :
    ∀ᶠ N : ℕ in atTop,
      (1 / 1000000 : ℝ) * lowerProfile N < firstException N ∧
      (firstException N : ℝ) ≤ 128 * N / Real.log (N : ℝ) :=
  eventually_strict_lower_bound.and eventually_explicit_upper_bound

/-- The quantified comparison form of the original resolved estimate. -/
theorem liu_sawhney_resolution :
    ∃ (k : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        c * Erdos294.lowerProfile k N ≤ firstException N ∧
        (firstException N : ℝ) ≤ C * Erdos294.upperProfile N := by
  refine ⟨20, 1 / 1000000, 128, by norm_num, by norm_num, ?_⟩
  filter_upwards [jsp_000250] with N hN
  refine ⟨by simpa only [lowerProfile_eq_upstream] using hN.1.le, ?_⟩
  simpa only [Erdos294.upperProfile, mul_div_assoc] using hN.2

end JSP000250
