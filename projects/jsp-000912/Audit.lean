import FullProof

#print JSP912.erdos_1099
#print axioms JSP912.grid_approx
#print axioms JSP912.partialProd_bound
#print axioms JSP912.lower_gap_weight
#print axioms JSP912.all_gap_cost
#print axioms JSP912.hAlpha_candidate_bound
#print axioms JSP912.jsp_000912_full
#print axioms JSP912.erdos_1099

example : ∀ α : ℝ, α > 1 → ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ,
    n ≥ N ∧ JSP912.hAlpha α n ≤ C := JSP912.erdos_1099

-- A direct check of the exact complete-list definition.
example (α : ℝ) (n : ℕ) : JSP912.hAlpha α n =
    ((((Nat.divisors n).sort (· ≤ ·)).zip ((Nat.divisors n).sort (· ≤ ·)).tail).map
      (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum := rfl

-- Strictly positive witnesses, not a zero-divisor convention loophole.
example (α : ℝ) (hα : 1 < α) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    ∃ n : ℕ, 0 < n ∧ N ≤ n ∧ JSP912.hAlpha α n ≤ C := JSP912.jsp_000912_full α hα
