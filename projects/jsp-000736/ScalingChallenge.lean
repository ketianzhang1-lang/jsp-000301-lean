import JSP000736Scaling

/- Direct mathematical reading of the supplement, using a separate copy of
   the source factor-difference definition. -/
namespace ScalingOriginalStatement

def D (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

example (M : ℕ) : ∃ Ns Ds : Finset ℕ, Ns.card = 4 ∧ Ds.card = 4 ∧
    (∀ n ∈ Ns, M < n) ∧ (∀ d ∈ Ds, M < d) ∧
    (↑Ds : Set ℕ) ⊆ ⋂ n ∈ Ns, D n :=
  JSP000736.k_eq_4_above_every_bound M

example : {Ns : Finset ℕ | (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 4 ∧
    (⋂ n ∈ Ns, D n).ncard ≥ 4}.Infinite :=
  JSP000736.infinitely_many_k_eq_4_witnesses

end ScalingOriginalStatement
