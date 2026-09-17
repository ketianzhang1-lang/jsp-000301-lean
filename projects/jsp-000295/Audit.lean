import JSP000295
import Compatibility

#print JSP000295.HasDistinctSums
#print JSP000295.f
#print JSP000295.entry
#print JSP000295.lower_bound
#print Erdos357.erdos_357.variants.weisenberg
#print axioms JSP000295.blocks_injective
#print axioms JSP000295.entry_hasDistinctSums
#print axioms JSP000295.admissible_length_le
#print axioms JSP000295.lower_bound_of_square_le
#print axioms JSP000295.lower_bound
#print axioms JSP000295.real_lower_bound
#print axioms JSP000295.weisenberg
#print axioms Erdos357.erdos_357.variants.weisenberg
#print axioms Erdos357.explicit_lower_bound

example : ∀ n : ℕ, 2 * n.sqrt - 1 ≤ Erdos357.f n :=
  Erdos357.explicit_lower_bound
