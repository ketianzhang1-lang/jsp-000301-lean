import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# JSP-000390 / Erdős 479: the known k = -1 special case

This file proves an infinite family for k = -1 only. It does not prove
Graham's assertion for every integer k different from 1, nor claim new mathematics.
The mathematical special case is credited in the JSP catalog to Graham,
D. H. Lehmer and E. Lehmer; the elementary powers-of-three family is classical.
Prepared with OpenAI ChatGPT assistance under the submitting account's direction.
-/

namespace JSP000390

/-- Positive natural-number moduli solving the prescribed integer congruence.
The value -1 is a residue representative, not a negative Euclidean remainder. -/
def Solutions (k : ℤ) : Set ℕ :=
  {n | 0 < n ∧ (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)]}

/-- A cubic lifting step, proved by polynomial algebra over the integers. -/
lemma cube_lift {x d : ℤ} (hd : d ∣ x + 1) (h3 : (3 : ℤ) ∣ x + 1) :
    3 * d ∣ x ^ 3 + 1 := by
  obtain ⟨a, ha⟩ := hd
  obtain ⟨b, hb⟩ := h3
  have hx : x = 3 * b - 1 := by omega
  have hc : x ^ 2 - x + 1 = 3 * (3 * b ^ 2 - 3 * b + 1) := by
    rw [hx]
    ring
  refine ⟨a * (3 * b ^ 2 - 3 * b + 1), ?_⟩
  calc
    x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by ring
    _ = (d * a) * (3 * (3 * b ^ 2 - 3 * b + 1)) := by rw [ha, hc]
    _ = 3 * d * (a * (3 * b ^ 2 - 3 * b + 1)) := by ring

/-- A strengthened divisibility statement for the explicit infinite family. -/
theorem three_pow_succ_dvd (r : ℕ) :
    (3 : ℤ) ^ (r + 1) ∣ (2 : ℤ) ^ (3 ^ r : ℕ) + 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have h3 : (3 : ℤ) ∣ (2 : ℤ) ^ (3 ^ r : ℕ) + 1 := by
      apply dvd_trans ?_ ih
      refine ⟨(3 : ℤ) ^ r, ?_⟩
      rw [pow_succ]
      ring
    have hlift := cube_lift ih h3
    change (3 : ℤ) ^ ((r + 1) + 1) ∣ (2 : ℤ) ^ (3 ^ (r + 1) : ℕ) + 1
    rw [pow_succ (3 : ℤ) (r + 1), pow_succ (3 : ℕ) r, pow_mul]
    simpa only [mul_comm] using hlift

/-- Every power of three is a modulus with residue -1. -/
theorem three_pow_is_solution (r : ℕ) :
    (2 : ℤ) ^ (3 ^ r : ℕ) ≡ -1 [ZMOD ((3 ^ r : ℕ) : ℤ)] := by
  have hdiv : (3 : ℤ) ^ r ∣ (2 : ℤ) ^ (3 ^ r : ℕ) + 1 := by
    apply dvd_trans ?_ (three_pow_succ_dvd r)
    exact ⟨3, pow_succ (3 : ℤ) r⟩
  rw [Int.modEq_iff_dvd]
  have hcast : ((3 ^ r : ℕ) : ℤ) = (3 : ℤ) ^ r := by simp
  rw [hcast]
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨-q, ?_⟩
  calc
    -1 - (2 : ℤ) ^ (3 ^ r : ℕ) = -((2 : ℤ) ^ (3 ^ r : ℕ) + 1) := by ring
    _ = -((3 : ℤ) ^ r * q) := by rw [hq]
    _ = (3 : ℤ) ^ r * (-q) := by ring

lemma lt_three_pow (r : ℕ) : r < 3 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [pow_succ]
    omega

/-- There is a nontrivial positive solution above every natural bound. -/
theorem minus_one_unbounded (B : ℕ) :
    ∃ n : ℕ, B < n ∧ 1 < n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] := by
  have hbound := lt_three_pow (B + 1)
  exact ⟨3 ^ (B + 1), by omega, by omega, three_pow_is_solution (B + 1)⟩

/-- Complete infinitude theorem for the k = -1 special case, with positivity. -/
theorem minus_one_infinite : (Solutions (-1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro B
  obtain ⟨n, hn, hpos, hcong⟩ := minus_one_unbounded B
  exact ⟨n, ⟨by omega, hcong⟩, hn⟩

/-- The same infinitude in the unbounded-set notation used by Formal Conjectures.
No theorem from a conjecture file is imported as a hypothesis. -/
theorem minus_one_infinite_unrestricted :
    {n : ℕ | (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)]}.Infinite := by
  exact minus_one_infinite.mono (fun _ hn => hn.2)

end JSP000390
