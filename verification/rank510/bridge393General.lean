import JSP000393General

/- The original source states the minimum problem for complex coefficients.
This specification deliberately uses Mathlib's Complex polynomial ring and
literal support-cardinality minimum, independently of the submitted names. -/
namespace Verify393General
open Polynomial Filter
noncomputable section

def complexMinimum (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ P : ℂ[X], P.support.card = k ∧ (P ^ 2).support.card = m}

theorem minimum_definition (k : ℕ) :
    complexMinimum k = JSP000393General.minimumSquareTerms ℂ k := by
  rfl

theorem complex_attained (k : ℕ) :
    ∃ P : ℂ[X], P.support.card = k ∧ (P ^ 2).support.card = complexMinimum k := by
  exact JSP000393General.minimum_attained k

theorem intended :
    Tendsto complexMinimum atTop atTop ∧
    (∀ k : ℕ, complexMinimum (13 ^ k) ≤ 12 ^ k) ∧
    (∀ M N : ℕ, ∃ n : ℕ, N ≤ n ∧ M * complexMinimum n < n) := by
  exact JSP000393General.jsp_000393 (K := ℂ)

theorem complex_uniform_threshold (B : ℕ) (P : ℂ[X])
    (hP : 2 + 32 ^ (2 ^ B) ≤ P.support.card) :
    B < (P ^ 2).support.card :=
  JSP000393General.uniform_threshold B P hP

theorem complex_zero_and_one : complexMinimum 0 = 0 ∧ complexMinimum 1 = 1 := by
  have hzero : (0 : ℂ[X]).support.card = 0 := by
    rw [Polynomial.support_zero, Finset.card_empty]
  have hone : (1 : ℂ[X]).support.card = 1 := by
    rw [← Polynomial.C_1, Polynomial.support_C one_ne_zero, Finset.card_singleton]
  constructor
  · rw [minimum_definition]
    apply Nat.eq_zero_of_le_zero
    have h := JSP000393General.minimum_le (K := ℂ) (P := 0) hzero
    rw [zero_pow (by decide : 2 ≠ 0), hzero] at h
    exact h
  · rw [minimum_definition]
    apply Nat.le_antisymm
    · have h := JSP000393General.minimum_le (K := ℂ) (P := 1) hone
      rw [one_pow, hone] at h
      exact h
    · obtain ⟨P, hP, hP2⟩ := JSP000393General.minimum_attained (K := ℂ) 1
      have hPne : P ≠ 0 := by
        intro h
        rw [h, hzero] at hP
        omega
      have hsquare : P ^ 2 ≠ 0 := pow_ne_zero 2 hPne
      have hcard : 0 < (P ^ 2).support.card := by
        exact Nat.pos_of_ne_zero (fun h => hsquare (Polynomial.card_support_eq_zero.mp h))
      rw [hP2] at hcard
      exact hcard

end
end Verify393General
