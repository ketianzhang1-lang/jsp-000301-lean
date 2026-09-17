/-
Our integration and constructive consequences for JSP-000393.
Prepared for GitHub account ketianzhang1-lang with OpenAI ChatGPT assistance.
Schinzel's lower-bound proof is imported from the pinned, attributed plby source.
-/
import JSP000393
import ErdosProblems.Erdos485

namespace JSP000393Complete
open Polynomial Filter

noncomputable section

/-- Coercing integer coefficients to rationals preserves the actual support. -/
theorem integer_support (P : ℤ[X]) :
    (P.map (Int.castRingHom ℚ)).support = P.support :=
  Polynomial.support_map_of_injective P (by
    intro a b h
    change (a : ℚ) = (b : ℚ) at h
    exact_mod_cast h)

/-- Our previously checked family, viewed in the original rational coefficient ring. -/
def rationalFamily (k : ℕ) : ℚ[X] :=
  (JSP000393.family k).map (Int.castRingHom ℚ)

theorem rational_family_counts (k : ℕ) :
    Erdos485.termCount (rationalFamily k) = 13 ^ k ∧
    Erdos485.termCount (rationalFamily k ^ 2) = 12 ^ k := by
  have hs := JSP000393.family_counts k
  constructor
  · simpa [Erdos485.termCount, rationalFamily, integer_support] using hs.1
  · simpa only [Erdos485.termCount, rationalFamily, ← Polynomial.map_pow,
      integer_support] using hs.2

/-- The construction bounds the actual attained minimum in the original question. -/
theorem minimum_family_upper_bound (k : ℕ) :
    Erdos485.f (13 ^ k) ≤ 12 ^ k := by
  have h := Erdos485.f_minimal (rational_family_counts k).1
  rwa [(rational_family_counts k).2] at h

private theorem index_le_pow (k : ℕ) : k ≤ 13 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hp : 0 < 13 ^ k := pow_pos (by decide) _
    omega

/-- The small-ratio phenomenon occurs at arbitrarily large support sizes. -/
theorem arbitrarily_large_small_ratio (M N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ M * Erdos485.f n < n := by
  let k := 12 * (M + N + 1)
  refine ⟨13 ^ k, ?_, ?_⟩
  · exact (show N ≤ k by dsimp [k]; omega).trans (index_le_pow k)
  · have hupper := minimum_family_upper_bound k
    have hg := JSP000393.growth k
    have hp : 0 < 12 ^ k := pow_pos (by decide) _
    have hlarge : 12 * M ≤ k := by dsimp [k]; omega
    have hstrict : M * 12 ^ k < 13 ^ k := by nlinarith
    exact lt_of_le_of_lt (Nat.mul_le_mul_left M hupper) hstrict

/-- The imported complete Schinzel bound also applies to our integer model. -/
theorem integer_schinzel_bound (P : ℤ[X]) (hP : 2 ≤ P.support.card) :
    P.support.card ≤ 1 + 32 ^ (2 ^ (P ^ 2).support.card) := by
  have h := Erdos485.schinzel_term_bound (P.map (Int.castRingHom ℚ))
    (by simpa [Erdos485.termCount, integer_support] using hP)
  simpa only [Erdos485.termCount, ← Polynomial.map_pow, integer_support] using h

/-- A subtraction-free explicit threshold, uniform over all integer polynomials. -/
theorem integer_uniform_threshold (B : ℕ) (P : ℤ[X])
    (hP : 2 + 32 ^ (2 ^ B) ≤ P.support.card) :
    B < (P ^ 2).support.card := by
  by_contra h
  have hs := integer_schinzel_bound P ((Nat.le_add_right 2 _).trans hP)
  have hb : (P ^ 2).support.card ≤ B := by omega
  have hp : 32 ^ (2 ^ (P ^ 2).support.card) ≤ 32 ^ (2 ^ B) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hb)
  omega

/-- Complete original lower-bound question, from the attributed Schinzel development. -/
theorem minimum_diverges : Tendsto Erdos485.f atTop atTop :=
  Erdos485.erdos_485

/-- Full lower-bound resolution and our constructive consequences in one interface. -/
theorem jsp_000393 :
    Tendsto Erdos485.f atTop atTop ∧
    (∀ k : ℕ, Erdos485.f (13 ^ k) ≤ 12 ^ k) ∧
    (∀ M N : ℕ, ∃ n : ℕ, N ≤ n ∧ M * Erdos485.f n < n) :=
  ⟨minimum_diverges, minimum_family_upper_bound, arbitrarily_large_small_ratio⟩

end
end JSP000393Complete
