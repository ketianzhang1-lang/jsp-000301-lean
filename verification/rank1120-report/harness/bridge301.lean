import JSP000301

namespace Verify301

/-- Direct arithmetic support for the historical witness and the non-square interval. -/
theorem witness_arithmetic :
    12167 = (23 : ℕ) ^ 3 ∧
    12168 = (2 : ℕ) ^ 3 * ((3 : ℕ) ^ 2 * (13 : ℕ) ^ 2) ∧
    110 ^ 2 < (12167 : ℕ) ∧ (12168 : ℕ) < 111 ^ 2 := by
  norm_num

/-- Original positive-integer counterexample, with literal prime and square predicates. -/
theorem positive_pair :
    ∃ n : ℕ, 0 < n ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p * p ∣ n) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ n + 1 → p * p ∣ n + 1) ∧
      ¬ (∃ m : ℕ, m * m = n) ∧
      ¬ (∃ m : ℕ, m * m = n + 1) := by
  simpa only [JSP000301.Powerful, JSP000301.PerfectSquare, pow_two] using
    JSP000301.jsp_000301_counterexample

/-- The exact catalog yes/no assertion is false; no counting claim is substituted. -/
theorem original_question_false :
    ¬ (∀ n : ℕ, 0 < n →
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p * p ∣ n) →
      (∀ p : ℕ, Nat.Prime p → p ∣ n + 1 → p * p ∣ n + 1) →
      (∃ m : ℕ, m * m = n) ∨ (∃ m : ℕ, m * m = n + 1)) := by
  simpa only [JSP000301.Powerful, JSP000301.PerfectSquare, pow_two] using
    JSP000301.jsp_000301_disproved

end Verify301
