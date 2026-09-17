import StarSharpness

-- Statement check: the full universal target, with no hidden hypothesis.
set_option linter.unusedVariables false in
example : ∀ (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2 :=
  Erdos547.erdos_547

#print axioms Erdos548.tree_free_edge_bound
#print axioms JSP000438.trees_monochromatic
#print axioms JSP000438.tree_monochromatic
#print axioms JSP000438.graphRamsey_trees
#print axioms Erdos547.erdos_547

-- Sharpness endpoints: every even tree order, including order two.
#print axioms JSP000438.sharpGraph_degree_le
#print axioms JSP000438.sharpGraph_compl_degree_le
#print axioms JSP000438.sharpGraph_avoids_star
#print axioms JSP000438.star_ramsey_even_order
#print axioms JSP000438.tree_ramsey_bound_is_sharp

example (k : ℕ) :
    SimpleGraph.diagonalGraphRamsey (SimpleGraph.starGraph (0 : Fin (2 * k + 2))) =
      4 * k + 2 := JSP000438.star_ramsey_even_order k
