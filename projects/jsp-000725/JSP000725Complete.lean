import JSP000725Bridge
import ErdosProblems.Erdos874

/-! Complete resolution in our original natural-number formulation.
The arbitrary-set upper bound is supplied by the attributed, pinned
Deshouillers--Freiman development. Our original interval construction is
used directly as the maximizing witness; no unproved structural premise
is assumed by the final theorem. -/

namespace JSP000725
open Finset Filter
open scoped Topology

def terminalInterval (N : ℕ) : Finset ℕ :=
  Icc (N - (Nat.sqrt (4 * N + 1) - 1) + 1) N

theorem strausLength_feasible (N : ℕ) :
    (Nat.sqrt (4 * N + 1) - 1 + 1)^2 ≤ 4 * N + 1 := by
  have hs : 1 ≤ Nat.sqrt (4 * N + 1) := by rw [Nat.le_sqrt]; omega
  rw [Nat.sub_add_cancel hs]
  exact Nat.sqrt_le' _

/-- Our explicit witness is valid for every N, including N = 0. -/
theorem terminalInterval_spec (N : ℕ) :
    terminalInterval N ⊆ Icc 1 N ∧ Admissible (terminalInterval N) ∧
      (terminalInterval N).card = Nat.sqrt (4 * N + 1) - 1 := by
  have hb := strausLength_feasible N
  have hm := length_le_endpoint hb
  refine ⟨?_, interval_admissible N _ hm hb, interval_card N _ hm⟩
  intro x hx
  have := mem_Icc.mp hx
  exact mem_Icc.mpr ⟨by omega, this.2⟩

theorem card_le_maxCard {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (ha : Admissible A) : A.card ≤ maxCard N := by
  exact Finset.le_sup (mem_admissibleFamily.mpr ⟨hA, ha⟩)

/-- The exact extremal value for all sufficiently large ambient intervals. -/
theorem eventual_maxCard_exact :
    ∀ᶠ N : ℕ in atTop, maxCard N = Nat.sqrt (4 * N + 1) - 1 := by
  filter_upwards [Erdos874.erdos_874_eventual_exact] with N hN
  simpa only [maxCard_eq_upstream, Erdos874.strausLength] using hN

/-- Our original interval witness is eventually optimal among all admissible sets. -/
theorem eventual_terminalInterval_optimal :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Icc 1 N → Admissible A → A.card ≤ (terminalInterval N).card := by
  filter_upwards [eventual_maxCard_exact] with N hN A hA ha
  rw [(terminalInterval_spec N).2.2, ← hN]
  exact card_le_maxCard hA ha

theorem maxCard_asymptotic :
    Tendsto (fun N : ℕ ↦ (maxCard N : ℝ) / Real.sqrt N) atTop (𝓝 2) := by
  simpa only [maxCard_eq_upstream] using Erdos874.erdos_874

/-- Complete original-scope statement: an all-N witness, eventual optimality
against arbitrary sets, and the sharp asymptotic constant 2. -/
theorem jsp_000725 :
    (∀ N : ℕ, terminalInterval N ⊆ Icc 1 N ∧ Admissible (terminalInterval N) ∧
      (terminalInterval N).card = Nat.sqrt (4 * N + 1) - 1) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Icc 1 N → Admissible A → A.card ≤ (terminalInterval N).card) ∧
    Tendsto (fun N : ℕ ↦ (maxCard N : ℝ) / Real.sqrt N) atTop (𝓝 2) := by
  exact ⟨terminalInterval_spec, eventual_terminalInterval_optimal, maxCard_asymptotic⟩

end JSP000725
