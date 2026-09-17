import JSP000881
open scoped ArithmeticFunction.sigma
example (N : ℕ) : 76*(N/270) ≤ JSP000881.S N := JSP000881.block_lower_bound N
example (x : ℝ) (hx : 0 ≤ x) : (38/135 : ℝ)*x-76 ≤ JSP000881.SReal x :=
  JSP000881.original_real_lower_bound x hx
example (ε : ℝ) (hε : 0 < ε) : ∃ X : ℝ, 0 < X ∧
    ∀ x : ℝ, X ≤ x → (38/135 : ℝ)-ε ≤ JSP000881.SReal x/x :=
  JSP000881.asymptotic_lower_bound ε hε
example : JSP000881.S 0 = 0 := by decide
example : JSP000881.S 3 = 2 := by decide
#print axioms JSP000881.scale_solution
#print axioms JSP000881.seed_one_two
#print axioms JSP000881.seed_four_five
#print axioms JSP000881.witness_injective
#print axioms JSP000881.block_lower_bound
#print axioms JSP000881.linear_lower_bound
#print axioms JSP000881.realCount_eq
#print axioms JSP000881.original_real_lower_bound
#print axioms JSP000881.asymptotic_lower_bound
#print axioms JSP000881.infinitely_many_solutions
