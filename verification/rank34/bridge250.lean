import JSP000250Complete

open Filter
open scoped BigOperators
namespace Verify250

def SequenceOne (N t : ℕ) : Prop :=
  0 < t ∧ ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
    StrictMono n ∧ n 0 = t ∧ (∀ i, n i ≤ N) ∧ ∑ i, (1 : ℚ) / n i = 1

theorem sequence_iff (N t : ℕ) :
    SequenceOne N t ↔ JSP000250.Representable N t := by
  simpa only [SequenceOne, Erdos294.SequenceRepresents, Nat.succ_le_iff] using
    (JSP000250.representable_iff_increasing_sequence N t).symm

theorem intended :
    ∀ᶠ N : ℕ in atTop, ∃ t : ℕ,
      0 < t ∧ ¬ SequenceOne N t ∧
      (∀ s : ℕ, 0 < s → s < t → SequenceOne N s) ∧
      (1 / 1000000 : ℝ) * ((N : ℝ) /
        (Real.log (N : ℝ) * (Real.log (Real.log (N : ℝ))) ^ 3 *
          (Real.log (Real.log (Real.log (N : ℝ)))) ^ 20)) < (t : ℝ) ∧
      (t : ℝ) ≤ 128 * N / Real.log (N : ℝ) := by
  filter_upwards [JSP000250.jsp_000250] with N hN
  refine ⟨JSP000250.firstException N, (JSP000250.firstException_spec N).1, ?_, ?_, ?_, hN.2⟩
  · intro h
    exact (JSP000250.firstException_spec N).2 ((sequence_iff N _).mp h)
  · intro s hs hst
    exact (sequence_iff N s).mpr (JSP000250.smaller_denominators_representable N s hs hst)
  · simpa only [JSP000250.lowerProfile] using hN.1

end Verify250
