/-
Copyright (c) 2026 ketianzhang1-lang. Released under the MIT license.
Prepared with OpenAI ChatGPT/Codex assistance.

This extension supplies the general characteristic-zero coefficient domain
required by the original complex-coefficient formulation of Erdős 485.
The algebraic reduction and its proof are reused, with full attribution,
from the pinned plby Erdos485 development by Codex / GPT-5.6 Sol.
Mathematical lower-bound credit remains with Andrzej Schinzel.
-/
import JSP000393Complete

namespace JSP000393General
open Polynomial Filter
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- General-field induction over the already-proved Schinzel reduction. -/
theorem schinzel_support_bound (P : K[X]) (hP : 2 ≤ P.support.card) :
    P.support.card ≤ Erdos485.B (P ^ 2).support.card := by
  generalize ht : (P ^ 2).support.card = t
  induction t using Nat.strong_induction_on generalizing P with
  | h t ih =>
      have ht3 : 3 ≤ t := by
        rw [← ht]
        exact Erdos485.three_le_sq_support_card hP
      obtain ⟨N⟩ := Erdos485.exists_primitiveNormalization P hP
      have hNt : (N.poly ^ 2).support.card = t := by
        rw [N.card_sq_support_eq, ht]
      by_cases htbase : t = 3
      · have htwo : N.poly.support.card = 2 :=
          Erdos485.primitive_trinomial_support_card_eq_two N N.two_le_support
            (hNt.trans htbase)
        have hPtwo : P.support.card = 2 := by
          rw [← N.card_support_eq]
          exact htwo
        simp [hPtwo, htbase]
      · have ht4 : 4 ≤ t := by omega
        have hNfour : 4 ≤ (N.poly ^ 2).support.card := by rwa [hNt]
        rcases Erdos485.primitiveNormalization_deformation N hNfour with
          hsmall | hdeform
        · have hsmall' : P.support.card ≤ 1 + 8 ^ (t - 2) / 2 := by
            simpa only [N.card_support_eq, hNt] using hsmall
          exact hsmall'.trans (Erdos485.all_zero_estimate ht4)
        · obtain ⟨D⟩ := hdeform
          obtain ⟨F, c, hc, hsquare⟩ := D.exists_eq_scalar_mul_sq N
          obtain ⟨G, hG, hGsq, hPG⟩ :=
            Erdos485.deformation_recursive_step_of_scalar_square D c hc F hsquare
          have hGt : (G ^ 2).support.card < t := by simpa only [hNt] using hGsq
          have hPG' : P.support.card ≤ G.support.card ^ 2 := by
            simpa only [N.card_support_eq] using hPG
          have hGB : G.support.card ≤ Erdos485.B (G ^ 2).support.card :=
            ih (G ^ 2).support.card hGt G hG rfl
          have hGpred : (G ^ 2).support.card ≤ t - 1 := by omega
          have hGBpred : G.support.card ≤ Erdos485.B (t - 1) :=
            hGB.trans (Erdos485.B_mono hGpred)
          exact (hPG'.trans (Nat.pow_le_pow_left hGBpred 2)).trans
            (Nat.le_of_lt (Erdos485.B_pred_sq_lt ht4))

theorem schinzel_term_bound (P : K[X]) (hP : 2 ≤ P.support.card) :
    P.support.card ≤ 1 + 32 ^ (2 ^ (P ^ 2).support.card) :=
  (schinzel_support_bound P hP).trans (Erdos485.B_le_coarse _)

theorem uniform_threshold (B : ℕ) (P : K[X])
    (hP : 2 + 32 ^ (2 ^ B) ≤ P.support.card) :
    B < (P ^ 2).support.card := by
  by_contra h
  have hs := schinzel_term_bound P ((Nat.le_add_right 2 _).trans hP)
  have hb : (P ^ 2).support.card ≤ B := by omega
  have hp : 32 ^ (2 ^ (P ^ 2).support.card) ≤ 32 ^ (2 ^ B) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hb)
  omega

/-- The actual minimum of squared support sizes over the specified field. -/
def minimumSquareTerms (K : Type*) [Field K] (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ P : K[X], P.support.card = k ∧ (P ^ 2).support.card = m}

theorem minimum_attained (k : ℕ) :
    ∃ P : K[X], P.support.card = k ∧
      (P ^ 2).support.card = minimumSquareTerms K k := by
  have hnonempty :
      {m : ℕ | ∃ P : K[X], P.support.card = k ∧ (P ^ 2).support.card = m}.Nonempty := by
    obtain ⟨Q, hQ, _⟩ := Erdos485.f_attained k
    let P : K[X] := Q.map (algebraMap ℚ K)
    refine ⟨(P ^ 2).support.card, P, ?_, rfl⟩
    change (Q.map (algebraMap ℚ K)).support.card = k
    rw [Polynomial.support_map_of_injective Q (RingHom.injective _)]
    exact hQ
  simpa only [minimumSquareTerms, Set.mem_ofPred_eq] using Nat.sInf_mem hnonempty

omit [CharZero K] in
theorem minimum_le {k : ℕ} {P : K[X]} (hP : P.support.card = k) :
    minimumSquareTerms K k ≤ (P ^ 2).support.card :=
  Nat.sInf_le ⟨P, hP, rfl⟩

theorem minimum_diverges : Tendsto (minimumSquareTerms K) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  refine ⟨2 + 32 ^ (2 ^ B), ?_⟩
  intro k hk
  obtain ⟨P, hP, hsquare⟩ := minimum_attained (K := K) k
  have hlarge : 2 + 32 ^ (2 ^ B) ≤ P.support.card := by rwa [hP]
  have h := uniform_threshold B P hlarge
  rw [hsquare] at h
  exact Nat.le_of_lt h

/-- The original integer construction transported by an injective field map. -/
def family (K : Type*) [Field K] [CharZero K] (k : ℕ) : K[X] :=
  (JSP000393Complete.rationalFamily k).map (algebraMap ℚ K)

theorem family_counts (k : ℕ) :
    (family K k).support.card = 13 ^ k ∧
    (family K k ^ 2).support.card = 12 ^ k := by
  have h := JSP000393Complete.rational_family_counts k
  constructor
  · change ((JSP000393Complete.rationalFamily k).map (algebraMap ℚ K)).support.card = _
    rw [Polynomial.support_map_of_injective _ (RingHom.injective (algebraMap ℚ K))]
    exact h.1
  · change ((JSP000393Complete.rationalFamily k).map (algebraMap ℚ K) ^ 2).support.card = _
    rw [← Polynomial.map_pow,
      Polynomial.support_map_of_injective _ (RingHom.injective (algebraMap ℚ K))]
    exact h.2

theorem minimum_family_upper_bound (k : ℕ) :
    minimumSquareTerms K (13 ^ k) ≤ 12 ^ k := by
  have h := minimum_le (family_counts (K := K) k).1
  rwa [(family_counts (K := K) k).2] at h

private theorem index_le_pow (k : ℕ) : k ≤ 13 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 13 ^ k := pow_pos (by decide) _
      omega

theorem arbitrarily_large_small_ratio (M N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ M * minimumSquareTerms K n < n := by
  let k := 12 * (M + N + 1)
  refine ⟨13 ^ k, ?_, ?_⟩
  · exact (show N ≤ k by dsimp [k]; omega).trans (index_le_pow k)
  · have hupper := minimum_family_upper_bound (K := K) k
    have hg := JSP000393.growth k
    have hp : 0 < 12 ^ k := pow_pos (by decide) _
    have hlarge : 12 * M ≤ k := by dsimp [k]; omega
    have hstrict : M * 12 ^ k < 13 ^ k := by nlinarith
    exact lt_of_le_of_lt (Nat.mul_le_mul_left M hupper) hstrict

/-- Complete original scope, including complex coefficients. -/
theorem jsp_000393 :
    Tendsto (minimumSquareTerms K) atTop atTop ∧
    (∀ k : ℕ, minimumSquareTerms K (13 ^ k) ≤ 12 ^ k) ∧
    (∀ M N : ℕ, ∃ n : ℕ, N ≤ n ∧ M * minimumSquareTerms K n < n) :=
  ⟨minimum_diverges, minimum_family_upper_bound, arbitrarily_large_small_ratio⟩

theorem complex_original :
    Tendsto (fun k : ℕ =>
      sInf {m : ℕ | ∃ P : ℂ[X], P.support.card = k ∧ (P ^ 2).support.card = m})
      atTop atTop :=
  minimum_diverges (K := ℂ)

end
end JSP000393General
