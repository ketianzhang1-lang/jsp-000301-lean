import JSP000725Complete

namespace Verify725
open Finset Filter
open scoped Topology

-- Independent literal subset-sum formulation: empty and overlapping subsets
-- are allowed; each summand occurs only once in each finite subset.
def Admissible (A : Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → ∀ T : Finset ℕ, T ⊆ A →
    (∑ x ∈ S, x) = (∑ x ∈ T, x) → S.card = T.card

noncomputable def maximum (N : ℕ) : ℕ := by
  classical
  exact ((Icc 1 N).powerset.filter Admissible).sup Finset.card

theorem admissible_iff (A : Finset ℕ) :
    Admissible A ↔ JSP000725.Admissible A := Iff.rfl

theorem all_N_witness (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ Admissible A ∧
      A.card = Nat.sqrt (4 * N + 1) - 1 := by
  exact JSP000725.construction_for_every_N N

theorem maximum_eq (N : ℕ) : maximum N = JSP000725.maxCard N := rfl

theorem eventual_arbitrary_set_bound :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Icc 1 N → Admissible A → A.card ≤ Nat.sqrt (4 * N + 1) - 1 := by
  filter_upwards [JSP000725.eventual_maxCard_exact] with N hN
  intro A hA ha
  rw [← hN]
  exact JSP000725.card_le_maxCard hA ha

theorem eventual_attained_maximum :
    ∀ᶠ N : ℕ in atTop,
      maximum N = Nat.sqrt (4 * N + 1) - 1 ∧
      ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ Admissible A ∧ A.card = maximum N := by
  filter_upwards [JSP000725.eventual_maxCard_exact] with N hN
  have he : maximum N = Nat.sqrt (4 * N + 1) - 1 := hN
  refine ⟨he, ?_⟩
  obtain ⟨A, hA, ha, hc⟩ := all_N_witness N
  exact ⟨A, hA, ha, hc.trans he.symm⟩

theorem sharp_asymptotic :
    Tendsto (fun N : ℕ => (maximum N : ℝ) / Real.sqrt N) atTop (𝓝 2) := by
  exact JSP000725.maxCard_asymptotic

end Verify725
