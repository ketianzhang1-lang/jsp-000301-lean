import Main
import Mathlib.Data.Nat.PrimeFin

namespace JSP000780General

/-- The prime-factor formulation in the pinned source problem. -/
def FactorFull (r n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^r ∣ n

lemma full_iff_factorFull (r n : ℕ) : Full r n ↔ FactorFull r n := by
  constructor
  · intro h p hp
    have hm := Nat.mem_primeFactors.mp hp
    exact h p hm.1 hm.2.1
  · intro h p hp hd
    by_cases hn : n = 0
    · simp only [hn, dvd_zero]
    · exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)

def OriginalSolutions (r : ℕ) : Set (Finset ℕ) :=
  {s | s.card = r-2 ∧ s.gcd id = 1 ∧ FactorFull r (∑ n ∈ s, n) ∧
    ∀ n ∈ s, 0 < n ∧ FactorFull r n}

lemma solutions_eq_original (r : ℕ) : Solutions r = OriginalSolutions r := by
  ext s
  simp only [Solutions, OriginalSolutions, Set.mem_ofPred_eq, ← full_iff_factorFull]

theorem original_all_r_infinite : ∀ r ≥ 6, (OriginalSolutions r).Infinite := by
  intro r hr
  rw [← solutions_eq_original]
  exact infinitely_many_solutions r hr

theorem original_every_parameter (r t : ℕ) (hr : 6 ≤ r) :
    terms r t ∈ OriginalSolutions r := by
  rw [← solutions_eq_original]
  exact solution_for_every_parameter r t hr

end JSP000780General
