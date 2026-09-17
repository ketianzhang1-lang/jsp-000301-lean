import JSP000736

/- Independently restate the upstream definition and k = 4 statement.
   Source: FormalConjectures/ErdosProblems/885.lean at
   c252a41054125b5fd9c8356e2137cd9b55337657. Apache-2.0.
   Copyright 2026 The Formal Conjectures Authors. -/
namespace OriginalStatement

def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

example : ∃ Ns : Finset ℕ,
    (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 4 ∧
    (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 :=
  JSP000736.erdos_885_k_eq_4

end OriginalStatement
