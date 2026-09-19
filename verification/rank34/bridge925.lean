import JSP000925Strict

open Polynomial Set
namespace Verify925

theorem intended {N : ℕ} (hN : 0 < N) {a d : ℝ} (hd : 0 < d)
    {f : ℝ[X]} (hf : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j : ℕ, j ≤ N → f.eval (a + d * j) = 0) :
    ∃ b : ℕ → ℝ,
      (∀ k, k < N → a + d * k < b k ∧ b k < a + d * (k + 1)) ∧
      (∀ k, k < N → f.derivative.eval (b k) = 0) ∧
      (∀ k, k < N → ∀ x, a + d * k < x ∧ x < a + d * (k + 1) →
        f.derivative.eval x = 0 → x = b k) ∧
      (∀ i, i + 2 < N → N ≤ 2 * (i + 1) →
        b (i + 1) - b i < b (i + 2) - b (i + 1)) ∧
      (∀ i, i + 1 < N →
        b (i + 1) - b i = b (N - 1 - i) - b (N - 2 - i)) := by
  simpa only [JSP000925Strict.RightGapStrict, Erdos1114.GapSymmetric,
    Set.mem_Ioo] using
    (JSP000925Strict.exists_unique_strict_gaps hN hd hf hdegree hroots)

end Verify925
