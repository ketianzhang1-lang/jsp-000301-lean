import Main

example :
    {n : ℕ | n ≤ 2 ^ 44 ∧ 2 < n ∧
      ∀ k, 0 < k → 2 ^ k < n → Nat.Prime (n - 2 ^ k)} =
      ({4, 7, 15, 21, 45, 75, 105} : Set ℕ) :=
  JSP000947.mientka_weitzenkamp

#print axioms JSP000947.not_good_of_bad
#print axioms JSP000947.checkTree_join
#print axioms JSP000947.checkTree_sound
#print axioms JSP000947.forced_divisor
#print axioms JSP000947.certificate2
#print axioms JSP000947.certificate3
#print axioms JSP000947.certificate4
#print axioms JSP000947.certificate5
#print axioms JSP000947.certificate6
#print axioms JSP000947.certificate7
#print axioms JSP000947.classification
#print axioms JSP000947.mientka_weitzenkamp
