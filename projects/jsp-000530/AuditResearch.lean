import JSP000530Research

open JSP000530 JSP000530.Research

example (S : Finset ℂ) (p : ℂ) (hS : NoFourConcyclic S) (hp : p ∈ S) :
    S.card - 1 ≤ 3 * (distanceValues S p).card := one_third_bound hS hp

example : UniformDistanceImprovement ↔ UniformSlackImprovement :=
  uniform_improvement_iff_slack

example (t : ℝ) (ht : t ≠ 0) : ¬ NoFourConcyclic (fourBentPoints t) :=
  quadratic_bending_not_no_four ht

#print axioms JSP000530.Research.distance_fiber_le_three
#print axioms JSP000530.Research.sum_distance_fibers
#print axioms JSP000530.Research.slack_eq_small_fibers
#print axioms JSP000530.Research.slack_identity
#print axioms JSP000530.Research.one_third_bound
#print axioms JSP000530.Research.slack_identity_real
#print axioms JSP000530.Research.improvement_iff_linear_slack
#print axioms JSP000530.Research.uniform_improvement_iff_slack
#print axioms JSP000530.Research.equidistant_centers_collinear
#print axioms JSP000530.Research.equidistant_centers_le_two
#print axioms JSP000530.Research.bent_cross_difference
#print axioms JSP000530.Research.bending_breaks_cross_pair
#print axioms JSP000530.Research.distance_eq_of_sqDist_eq
#print axioms JSP000530.Research.bent_symmetric_circle
#print axioms JSP000530.Research.quadratic_bending_not_no_four
