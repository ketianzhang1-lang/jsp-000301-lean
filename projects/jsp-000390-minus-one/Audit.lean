import JSP000390
#print axioms JSP000390.three_pow_succ_dvd
#print axioms JSP000390.three_pow_is_solution
#print axioms JSP000390.minus_one_unbounded
#print axioms JSP000390.minus_one_infinite
#print axioms JSP000390.minus_one_infinite_unrestricted

-- Sanity checks: the modulus is positive and -1 is not confused with +1.
example : (2 : ℤ) ^ 3 ≡ -1 [ZMOD (3 : ℤ)] := by decide
example : ¬ ((2 : ℤ) ^ 3 ≡ (1 : ℤ) [ZMOD (3 : ℤ)]) := by decide
