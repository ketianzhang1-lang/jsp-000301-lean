import JSP000780

#print JSP000780.OriginalSolutions
#print JSP000780.Solution
#print JSP000780.base
#print JSP000780.terms
#print JSP000780.total
#print axioms JSP000780.solution_for_every_parameter
#print axioms JSP000780.terms_injective
#print axioms JSP000780.infinitely_many_solutions
#print axioms JSP000780.infinitely_many_totals
#print axioms JSP000780.original_six_infinite
#print axioms JSP000780.not_finite_for_every_r

example : ¬ ∀ r ≥ 4, (JSP000780.OriginalSolutions r).Finite :=
  JSP000780.not_finite_for_every_r

example : (JSP000780.OriginalSolutions 6).Infinite :=
  JSP000780.original_six_infinite
