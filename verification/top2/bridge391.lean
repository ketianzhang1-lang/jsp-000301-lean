import JSP000391Main

noncomputable section
namespace Verify391

-- Independently spelled out from Stoll's displayed recurrence, not an alias.
def recurrence (g : ℕ) (t e : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => if n % 2 = 0 then
      ⌊((g : ℝ) / (((g : ℝ) - 1) * (t + g))) * ((recurrence g t e n : ℝ) + e)⌋
    else
      ⌊(((g : ℝ) - 1) * (t + g)) * ((recurrence g t e n : ℝ) + 1 / ((g : ℝ) - 1))⌋

def radixDigit (g : ℕ) (t : ℝ) : ℕ → ℤ
  | 0 => ⌊t⌋
  | n + 1 => ⌊t * (g : ℝ) ^ (n + 1)⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n⌋

theorem recurrence_eq (g : ℕ) (t e : ℝ) (n : ℕ) :
    recurrence g t e n = JSP000391.sequence g t e n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recurrence, JSP000391.sequence, JSP000391.a, JSP000391.b, ih]

theorem digit_eq (g : ℕ) (t : ℝ) (n : ℕ) :
    radixDigit g t n = JSP000391.digit g t n := by
  cases n <;> rfl

theorem intended (g : ℕ) (w e : ℝ) (hg : 2 ≤ g) (hw : 0 < w)
    (he0 : -1 / (g : ℝ) ≤ e) (he1 : e < ((g : ℝ) + 1) * (g - 2) / g) :
    let t := w / (g : ℝ) ^ ⌊Real.logb (g : ℝ) w⌋
    ∀ n : ℕ, recurrence g t e (2*n+2) - (g : ℤ)*recurrence g t e (2*n) =
      radixDigit g t n := by
  simpa only [recurrence_eq, digit_eq, JSP000391.normalized] using
    (JSP000391.stoll_general_base g w e hg hw he0 he1).1

end Verify391
