import JSP001021

example : ∀ T : Erdos1216.Tournament 15,
    ∃ v : Fin 5 → Fin 15, Function.Injective v ∧
      ∀ i j : Fin 5, i < j → T.arc (v i) (v j) = true :=
  JSP001021.fifteen_vertices

example : ¬ (∀ n, 1 ≤ n → Erdos1216.f n = Nat.log2 n + 1) :=
  JSP001021.jsp_001021

#print axioms Erdos1216.directed_ramsey_five_fourteen
#print axioms Erdos1216.f_fourteen_eq_five
#print axioms Erdos1216.not_erdos_1216
#print axioms JSP001021.restrict14_arc
#print axioms JSP001021.all_orders
#print axioms JSP001021.fifteen_vertices
#print axioms JSP001021.five_le_f_fifteen
#print axioms JSP001021.jsp_001021
#print axioms JSP001021.LocalChecks.local_exclusions
#print axioms JSP001021.LocalChecks.retained_count
#print axioms JSP001021.LocalChecks.final_transitive_five
