import JSP000390Power
#print axioms JSP000390Power.power_tail_periodic
#print axioms JSP000390Power.exists_zmod_power_period
#print axioms JSP000390Power.power_residue_unbounded
#print axioms JSP000390Power.power_residue_infinite
#print axioms JSP000390Power.powers_of_two_infinite
#print axioms JSP000390Power.powers_of_two_infinite_unrestricted
#print axioms JSP000390Power.combined_known_families

-- Exact type checks use the original positive-modulus predicate.
example : ∀ i : ℕ, 0 < i → (JSP000390.Solutions ((2 : ℤ) ^ i)).Infinite :=
  JSP000390Power.powers_of_two_infinite
example : (JSP000390.Solutions ((2 : ℤ) ^ 3)).Infinite :=
  JSP000390Power.powers_of_two_infinite 3 (by decide)
