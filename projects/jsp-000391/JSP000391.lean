import Mathlib

/-!
# JSP-000391 / Erdos 482: Stoll's general-base digit recurrence

Original mathematics: Thomas Stoll, Journal of Integer Sequences 8 (2005),
Article 05.3.2, Theorem 1.3. This is an independently written Lean formalization,
prepared with OpenAI ChatGPT assistance, not a claim of new mathematics.

Indices are shifted by one: `sequence g t e 0` is the paper's u_1. Digits are
indexed from zero, starting with the leading significant digit of normalized t.
-/

noncomputable section
namespace JSP000391

/-- The first multiplier in Stoll's recurrence. -/
def a (g : ℕ) (t : ℝ) : ℝ := (g : ℝ) / (((g : ℝ) - 1) * (t + g))

/-- The second multiplier; equals g/a for the admissible parameters. -/
def b (g : ℕ) (t : ℝ) : ℝ := ((g : ℝ) - 1) * (t + g)

/-- A single alternating floor recurrence, not its purported closed form. -/
def sequence (g : ℕ) (t e : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => if n % 2 = 0 then
      ⌊a g t * ((sequence g t e n : ℝ) + e)⌋
    else
      ⌊b g t * ((sequence g t e n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-- An integer geometric sum, defined without truncated division. -/
def geometric (g : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (g : ℤ) * geometric g n + 1

/-- The ordinary finite digit prefix of a normalized real number. -/
def digitPrefix (g : ℕ) (t : ℝ) (n : ℕ) : ℤ := ⌊t * (g : ℝ) ^ n⌋

/-- Standard floor-difference digits, with the leading digit at index zero.
This definition fixes the terminating expansion convention at radix rationals. -/
def digit (g : ℕ) (t : ℝ) : ℕ → ℤ
  | 0 => ⌊t⌋
  | n + 1 => digitPrefix g t (n + 1) - (g : ℤ) * digitPrefix g t n

lemma geometric_relation (g n : ℕ) :
    ((g : ℝ) - 1) * (geometric g n : ℝ) = (g : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp [geometric]
  | succ n ih =>
    simp only [geometric, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      pow_succ]
    calc
      ((g : ℝ) - 1) * (g * (geometric g n : ℝ) + 1) =
          g * (((g : ℝ) - 1) * (geometric g n : ℝ)) + (g - 1) := by ring
      _ = g * ((g : ℝ) ^ n - 1) + (g - 1) := by rw [ih]
      _ = (g : ℝ) ^ n * g - 1 := by ring

lemma multipliers (g : ℕ) (t : ℝ) (hg : 2 ≤ g) (_ht : 1 ≤ t) :
    b g t = (g : ℝ) / a g t := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  simp [a, b, hg0]

lemma sequence_even (g : ℕ) (t e : ℝ) (n : ℕ) :
    sequence g t e (2 * n + 1) =
      ⌊a g t * ((sequence g t e (2 * n) : ℝ) + e)⌋ := by
  simp [sequence]

lemma sequence_odd (g : ℕ) (t e : ℝ) (n : ℕ) :
    sequence g t e (2 * n + 2) =
      ⌊b g t * ((sequence g t e (2 * n + 1) : ℝ) + 1 / ((g : ℝ) - 1))⌋ := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, sequence]
  norm_num [Nat.add_mod, Nat.mul_mod]

/-- The first, exceptional, step from the specified initial value. -/
lemma initial_floor (g : ℕ) (t e : ℝ) (hg : 2 ≤ g) (ht : 1 ≤ t)
    (he0 : -1 / (g : ℝ) ≤ e)
    (he1 : e < ((g : ℝ) + 1) * (g - 2) / g) :
    ⌊a g t * (1 + e)⌋ = (0 : ℤ) := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hD : 0 < ((g : ℝ) - 1) * (t + g) := mul_pos (by linarith) (by linarith)
  have hel := (div_le_iff₀ hgpos).mp he0
  have heu := (lt_div_iff₀ hgpos).mp he1
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_zero, zero_add]
  rw [a, div_mul_eq_mul_div]
  constructor
  · apply div_nonneg _ hD.le
    nlinarith
  · apply (div_lt_iff₀ hD).mpr
    nlinarith [mul_nonneg (show 0 ≤ (g : ℝ) - 1 by linarith) (show 0 ≤ t - 1 by linarith)]

/-- The expanding step evaluated on the actual integer geometric sum. -/
lemma expanding_floor (g : ℕ) (t : ℝ) (hg : 2 ≤ g) (n : ℕ) :
    ⌊b g t * ((geometric g n : ℝ) + 1 / ((g : ℝ) - 1))⌋ =
      ⌊(t + g) * (g : ℝ) ^ n⌋ := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hne : (g : ℝ) - 1 ≠ 0 := by linarith
  congr 1
  calc
    b g t * ((geometric g n : ℝ) + 1 / ((g : ℝ) - 1)) =
        (t + g) * (((g : ℝ) - 1) * (geometric g n : ℝ) + 1) := by
          dsimp [b]
          field_simp [hne]
    _ = (t + g) * (g : ℝ) ^ n := by rw [geometric_relation]; ring

/-- The contracting step; all floor errors are controlled explicitly. -/
lemma contracting_floor (g : ℕ) (t e : ℝ) (hg : 2 ≤ g) (ht : 1 ≤ t)
    (he0 : -1 / (g : ℝ) ≤ e)
    (he1 : e < ((g : ℝ) + 1) * (g - 2) / g) (n : ℕ) :
    ⌊a g t * ((⌊(t + g) * (g : ℝ) ^ n⌋ : ℤ) + e)⌋ = geometric g (n + 1) := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hD : 0 < ((g : ℝ) - 1) * (t + g) := mul_pos (by linarith) (by linarith)
  have hel := (div_le_iff₀ hgpos).mp he0
  have heu := (lt_div_iff₀ hgpos).mp he1
  have hf0 := Int.floor_le ((t + g) * (g : ℝ) ^ n)
  have hf1 := Int.lt_floor_add_one ((t + g) * (g : ℝ) ^ n)
  have hmul0 := mul_le_mul_of_nonneg_left hf0 hgpos.le
  have hmul1 := mul_lt_mul_of_pos_left hf1 hgpos
  have hr : (((g : ℝ) - 1) * (t + g)) * (geometric g (n + 1) : ℝ) =
      g * ((t + g) * (g : ℝ) ^ n) - (t + g) := by
    calc
      _ = (t + g) * (((g : ℝ) - 1) * (geometric g (n + 1) : ℝ)) := by ring
      _ = (t + g) * ((g : ℝ) ^ (n + 1) - 1) := by rw [geometric_relation]
      _ = _ := by rw [pow_succ]; ring
  apply Int.floor_eq_iff.mpr
  rw [a, div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hD).mpr
    nlinarith
  · apply (div_lt_iff₀ hD).mpr
    nlinarith [mul_nonneg (show 0 ≤ (g : ℝ) - 2 by linarith) (show 0 ≤ t - 1 by linarith)]

/-- Exact formulas for both subsequences, proved from the recurrence. -/
theorem sequence_closed_forms (g : ℕ) (t e : ℝ) (hg : 2 ≤ g) (ht : 1 ≤ t)
    (he0 : -1 / (g : ℝ) ≤ e)
    (he1 : e < ((g : ℝ) + 1) * (g - 2) / g) (n : ℕ) :
    sequence g t e (2 * n + 1) = geometric g n ∧
    sequence g t e (2 * n + 2) = ⌊(t + g) * (g : ℝ) ^ n⌋ := by
  induction n with
  | zero =>
    have hfirst : sequence g t e 1 = 0 := by
      simpa [sequence] using initial_floor g t e hg ht he0 he1
    constructor
    · simpa [geometric] using hfirst
    · rw [sequence_odd, hfirst]
      simpa [geometric] using expanding_floor g t hg 0
  | succ n ih =>
    have hfirst : sequence g t e (2 * (n + 1) + 1) = geometric g (n + 1) := by
      rw [sequence_even, show 2 * (n + 1) = 2 * n + 2 by omega, ih.2]
      exact contracting_floor g t e hg ht he0 he1 n
    constructor
    · exact hfirst
    · rw [sequence_odd, hfirst]
      exact expanding_floor g t hg (n + 1)

lemma expanded_prefix (g : ℕ) (t : ℝ) (n : ℕ) :
    ⌊(t + g) * (g : ℝ) ^ n⌋ = digitPrefix g t n + (g : ℤ) ^ (n + 1) := by
  rw [add_mul]
  have hp : (g : ℝ) * (g : ℝ) ^ n = ((g : ℤ) ^ (n + 1) : ℤ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [hp]
  apply Int.floor_eq_iff.mpr
  dsimp [digitPrefix]
  push_cast
  have hlo := Int.floor_le (t * (g : ℝ) ^ n)
  have hhi := Int.lt_floor_add_one (t * (g : ℝ) ^ n)
  constructor <;> linarith

/-- Stoll's Theorem 1.3 in normalized form, for all bases and all its shifts. -/
theorem recurrence_extracts_digits (g : ℕ) (t e : ℝ) (hg : 2 ≤ g)
    (ht0 : 1 ≤ t) (_ht1 : t < g)
    (he0 : -1 / (g : ℝ) ≤ e)
    (he1 : e < ((g : ℝ) + 1) * (g - 2) / g) (n : ℕ) :
    sequence g t e (2 * n + 2) - (g : ℤ) * sequence g t e (2 * n) = digit g t n := by
  cases n with
  | zero =>
    rw [(sequence_closed_forms g t e hg ht0 he0 he1 0).2, expanded_prefix]
    simp [sequence, digit, digitPrefix]
  | succ n =>
    rw [(sequence_closed_forms g t e hg ht0 he0 he1 (n + 1)).2,
      show 2 * (n + 1) = 2 * n + 2 by omega,
      (sequence_closed_forms g t e hg ht0 he0 he1 n).2,
      expanded_prefix, expanded_prefix, digit]
    rw [pow_succ]
    ring

/-- Each extracted digit is in the actual radix alphabet. -/
theorem digit_bounds (g : ℕ) (t : ℝ) (hg : 2 ≤ g) (ht0 : 1 ≤ t) (ht1 : t < g)
    (n : ℕ) : 0 ≤ digit g t n ∧ digit g t n < (g : ℤ) := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  cases n with
  | zero =>
    have hl := Int.floor_le t
    have hu := Int.lt_floor_add_one t
    have hlr : (-1 : ℝ) < (⌊t⌋ : ℝ) := by linarith
    have hur : (⌊t⌋ : ℝ) < (g : ℝ) := by linarith
    have hli : (-1 : ℤ) < ⌊t⌋ := by exact_mod_cast hlr
    have hui : ⌊t⌋ < (g : ℤ) := by exact_mod_cast hur
    dsimp [digit]
    omega
  | succ n =>
    have hl := Int.floor_le (t * (g : ℝ) ^ n)
    have hu := Int.lt_floor_add_one (t * (g : ℝ) ^ n)
    have hl' := Int.floor_le (t * (g : ℝ) ^ (n + 1))
    have hu' := Int.lt_floor_add_one (t * (g : ℝ) ^ (n + 1))
    have hml := mul_le_mul_of_nonneg_left hl (show 0 ≤ (g : ℝ) by positivity)
    have hmu := mul_lt_mul_of_pos_left hu (show 0 < (g : ℝ) by linarith)
    have hpow : t * (g : ℝ) ^ (n + 1) = g * (t * (g : ℝ) ^ n) := by rw [pow_succ]; ring
    rw [hpow] at hl' hu'
    have h0 : (-1 : ℝ) <
        (⌊t * (g : ℝ) ^ (n + 1)⌋ : ℝ) - g * (⌊t * (g : ℝ) ^ n⌋ : ℝ) := by
      rw [hpow]
      linarith
    have h1 : (⌊t * (g : ℝ) ^ (n + 1)⌋ : ℝ) -
        g * (⌊t * (g : ℝ) ^ n⌋ : ℝ) < g := by
      rw [hpow]
      linarith
    have h0i : (-1 : ℤ) < digit g t (n + 1) := by
      dsimp [digit, digitPrefix]
      exact_mod_cast h0
    have h1i : digit g t (n + 1) < (g : ℤ) := by
      dsimp [digit, digitPrefix]
      exact_mod_cast h1
    omega

end JSP000391
