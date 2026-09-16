import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace JSP000301

/-- A natural number is powerful (squareful) if every prime divisor occurs
with exponent at least two; equivalently, `p^2 ∣ n` for every prime `p ∣ n`. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- A natural number is a perfect square. -/
def PerfectSquare (n : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 2 = n

lemma powerful_12167 : Powerful 12167 := by
  intro p hp hpn
  have hfactor : 12167 = 23 ^ 3 := by
    norm_num
  rw [hfactor] at hpn
  have hp_eq : p = 23 :=
    Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hpn
  subst p
  norm_num

lemma powerful_12168 : Powerful 12168 := by
  intro p hp hpn
  have hfactor : 12168 = 2 ^ 3 * (3 ^ 2 * 13 ^ 2) := by
    norm_num
  rw [hfactor] at hpn
  rcases (hp.dvd_mul).mp hpn with h2 | hrest
  · have hp_eq : p = 2 :=
      Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h2
    subst p
    norm_num
  · rcases (hp.dvd_mul).mp hrest with h3 | h13
    · have hp_eq : p = 3 :=
        Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h3
      subst p
      norm_num
    · have hp_eq : p = 13 :=
        Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h13
      subst p
      norm_num

lemma not_square_12167 : ¬ PerfectSquare 12167 := by
  simpa [PerfectSquare] using
    (Nat.not_exists_sq' (m := 110) (n := 12167) (by norm_num) (by norm_num))

lemma not_square_12168 : ¬ PerfectSquare 12168 := by
  simpa [PerfectSquare] using
    (Nat.not_exists_sq' (m := 110) (n := 12168) (by norm_num) (by norm_num))

/-- Explicit counterexample to JSP-000301: 12167 and 12168 are consecutive
positive powerful numbers, and neither is a perfect square. -/
theorem jsp_000301_counterexample :
    ∃ n : ℕ,
      0 < n ∧
      Powerful n ∧
      Powerful (n + 1) ∧
      ¬ PerfectSquare n ∧
      ¬ PerfectSquare (n + 1) := by
  refine ⟨12167, by norm_num, powerful_12167, ?_, not_square_12167, ?_⟩
  · simpa using powerful_12168
  · simpa using not_square_12168

/-- A direct negation of the proposed universal assertion. -/
theorem jsp_000301_disproved :
    ¬ (∀ n : ℕ,
      0 < n →
      Powerful n →
      Powerful (n + 1) →
      PerfectSquare n ∨ PerfectSquare (n + 1)) := by
  intro h
  have hsquares :=
    h 12167 (by norm_num) powerful_12167 (by simpa using powerful_12168)
  rcases hsquares with hsq | hsq
  · exact not_square_12167 hsq
  · exact not_square_12168 (by simpa using hsq)

end JSP000301
