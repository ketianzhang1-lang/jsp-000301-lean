import Multicolor

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

#print axioms JSP000438.sum_edges_of_cover
#print axioms JSP000438.multicolor_trees_monochromatic
#print axioms JSP000438.multicolor_tree_embedding
#print axioms JSP000438.multicolorGraphRamsey_trees
