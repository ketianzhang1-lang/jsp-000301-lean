import JSP912.Main

namespace Verify912

/-- The literal complete-list expression, using only standard Mathlib divisors,
    sorted finite sets, list adjacency, real division and real powers. -/
noncomputable def divisorGapSum (α : ℝ) (n : ℕ) : ℝ :=
  let ds := (Nat.divisors n).sort (· ≤ ·)
  ((ds.zip ds.tail).map (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum

theorem literal_formula (α : ℝ) (n : ℕ) :
    JSP912.hAlpha α n = divisorGapSum α n := rfl

/-- Source-derived cofinal boundedness statement. Positive witnesses rule out
    Nat.divisors 0; the single C is chosen before every cutoff M. -/
theorem intended :
    ∀ α : ℝ, 1 < α → ∃ C : ℝ, 0 < C ∧
      ∀ M : ℕ, ∃ n : ℕ, 0 < n ∧ M ≤ n ∧ divisorGapSum α n < C := by
  intro α hα
  obtain ⟨C, hC, hw⟩ := JSP912.jsp_000912_full α hα
  refine ⟨C + 1, by linarith, ?_⟩
  intro M
  obtain ⟨n, hn, hMn, hb⟩ := hw M
  have hbound : divisorGapSum α n ≤ C := (literal_formula α n) ▸ hb
  exact ⟨n, hn, hMn, lt_of_le_of_lt hbound (by linarith)⟩

end Verify912
