import JSP000728
import ErdosProblems.Erdos877.Core

/-!
# Complete original counting question for JSP-000728 / Erdős 877

We connect our independently written lower-bound construction to the attributed
upstream upper-bound development. The source and compatibility changes of every
upstream module are pinned in UPSTREAM.json; no upper-bound hypothesis is added.
-/

open Filter
open scoped Topology

namespace JSP000728

theorem sumFree_iff_upstream (A : Finset ℕ) :
    SumFree A ↔ Erdos877.SumFree A := by
  constructor
  · intro h x y hx hy
    exact h x hx y hy
  · intro h x hx y hy
    exact h hx hy

theorem maximalSumFree_iff_upstream (N : ℕ) (A : Finset ℕ) :
    MaximalSumFree N A ↔ Erdos877.MaximalSumFreeIn (Erdos877.interval N) A := by
  constructor
  · rintro ⟨hA, hs, hm⟩
    refine ⟨hA, (sumFree_iff_upstream A).mp hs, ?_⟩
    intro B hB hBs hAB
    exact (hm B hB ((sumFree_iff_upstream B).mpr hBs) hAB).symm
  · rintro ⟨hA, hs, hm⟩
    refine ⟨hA, (sumFree_iff_upstream A).mpr hs, ?_⟩
    intro B hB hBs hAB
    exact (hm B hB ((sumFree_iff_upstream B).mp hBs) hAB).symm

theorem maximalSets_eq_upstream (N : ℕ) :
    maximalSets N = Erdos877.maximalSumFreeSets N := by
  ext A
  rw [mem_maximalSets, Erdos877.mem_maximalSumFreeSets, maximalSumFree_iff_upstream]

theorem maximalSets_card_eq_upstream (N : ℕ) :
    (maximalSets N).card = Erdos877.maximalSumFreeCount N := by
  rw [maximalSets_eq_upstream]
  rfl

/-- All sum-free subsets, with the same local predicate as our lower bound. -/
noncomputable def allSumFreeSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter SumFree

theorem allSumFreeSets_eq_upstream (N : ℕ) :
    allSumFreeSets N = Erdos877.sumFreeSets N := by
  classical
  ext A
  simp only [allSumFreeSets, Finset.mem_filter, Finset.mem_powerset,
    Erdos877.mem_sumFreeSets, Erdos877.interval, sumFree_iff_upstream]

/-- Subsets of the upper half supply the benchmark lower bound for all sets. -/
theorem upperHalf_powerset_subset (N : ℕ) :
    (Finset.Icc (N / 2 + 1) N).powerset ⊆ allSumFreeSets N := by
  classical
  intro A hA
  have hA' := Finset.mem_powerset.mp hA
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
  · intro x hx
    have h := Finset.mem_Icc.mp (hA' hx)
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  · intro x hx y hy hxy
    have h₁ := Finset.mem_Icc.mp (hA' hx)
    have h₂ := Finset.mem_Icc.mp (hA' hy)
    have h₃ := Finset.mem_Icc.mp (hA' hxy)
    omega

theorem allSumFreeSets_lower_bound (N : ℕ) :
    2 ^ (N - N / 2) ≤ (allSumFreeSets N).card := by
  have h := Finset.card_le_card (upperHalf_powerset_subset N)
  have hc : (Finset.Icc (N / 2 + 1) N).card = N - N / 2 := by
    rw [Nat.card_Icc]
    omega
  simpa only [Finset.card_powerset, hc] using h

theorem benchmark_le_allSumFreeSets (N : ℕ) :
    Real.rpow 2 ((N : ℝ) / 2) ≤ ((allSumFreeSets N).card : ℝ) := by
  have hn : N ≤ 2 * (N - N / 2) := by omega
  have hn' : (N : ℝ) ≤ 2 * ((N - N / 2 : ℕ) : ℝ) := by exact_mod_cast hn
  calc
    Real.rpow 2 ((N : ℝ) / 2) ≤ Real.rpow 2 ((N - N / 2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ) ^ (N - N / 2) := Real.rpow_natCast _ _
    _ ≤ ((allSumFreeSets N).card : ℝ) := by
      exact_mod_cast allSumFreeSets_lower_bound N

end JSP000728
