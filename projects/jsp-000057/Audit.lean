import JSP000057

example : Erdos20.f 2 3 = 7 := JSP000057.f_two_three

example (m : ℕ) :
    (∀ {α : Type}, ∀ (F : Set (Set α)),
      ((∀ A ∈ F, A.ncard = 2) ∧ m ≤ F.ncard) →
        ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S) ↔ 7 ≤ m :=
  JSP000057.original_threshold_iff m

#print axioms JSP000057.matching_of_card
#print axioms JSP000057.seven_forces_three
#print axioms JSP000057.twoTriangles_no_three
#print axioms JSP000057.threshold_iff
#print axioms JSP000057.seven_forces_three_sets
#print axioms JSP000057.twoTriangles_sets_no_three
#print axioms JSP000057.original_threshold_iff
#print axioms JSP000057.f_two_three
