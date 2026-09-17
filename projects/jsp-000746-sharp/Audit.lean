import JSP000746

example : ∀ G : SimpleGraph ℤ, G.CliqueFree 3 →
    ∃ a b c : ℤ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ c = a + b ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := JSP000746.jsp_000746

#print axioms Erdos895.erdos_895
#print axioms JSP000746Sharp.witness_triangle_free
#print axioms JSP000746Sharp.witness_no_independent_schur_triple
#print axioms JSP000746Sharp.counterexamples_below_eighteen
#print axioms JSP000746Sharp.exact_threshold
#print axioms JSP000746Sharp.least_threshold
#print axioms JSP000746.integer_graph
#print axioms JSP000746.jsp_000746
