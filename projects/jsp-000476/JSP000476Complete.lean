/-
Copyright 2026. Released under the Apache License 2.0.
Contribution: ketianzhang1-lang, with OpenAI ChatGPT assistance.
We prove statement correspondence and direct finite-set consequences of the
previously public complete plby/lean-proofs development. We retain upstream
authorship of that development and Nguyen--Vu's mathematical upper bound.
-/
import JSP000476
import ErdosProblems.Erdos587.AsymptoticBounds

open Finset Filter

namespace JSP000476

/-- Our original predicate is exactly the predicate used by the complete proof. -/
theorem squareSumFree_iff_upstream (A : Finset ℕ) :
    SquareSumFree A ↔ Erdos587.SquareSubsetSumFree A := by
  simp only [SquareSumFree, Erdos587.SquareSubsetSumFree,
    Finset.nonempty_iff_ne_empty, IsSquare, not_exists, pow_two]

/-- The maximum is taken over every admissible subset of the positive interval. -/
noncomputable def extremal (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter SquareSumFree).sup Finset.card

/-- The two maxima agree, including the empty interval and empty set. -/
theorem extremal_eq_upstream (N : ℕ) : extremal N = Erdos587.MaxNotSqSum N := by
  classical
  unfold extremal Erdos587.MaxNotSqSum
  apply congrArg (fun s : Finset (Finset ℕ) => s.sup Finset.card)
  exact Finset.filter_congr (fun A _ => squareSumFree_iff_upstream A)

theorem card_le_extremal {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : SquareSumFree A) : A.card ≤ extremal N := by
  rw [extremal_eq_upstream]
  exact Erdos587.card_le_maxNotSqSum hA ((squareSumFree_iff_upstream A).mp hfree)

theorem exists_extremizer (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, SquareSumFree A ∧ A.card = extremal N := by
  obtain ⟨A, hA, hfree, hcard⟩ := Erdos587.exists_admissible_card_eq N
  exact ⟨A, hA, (squareSumFree_iff_upstream A).mpr hfree,
    hcard.trans (extremal_eq_upstream N).symm⟩

theorem extremal_le_interval (N : ℕ) : extremal N ≤ N := by
  rw [extremal_eq_upstream]
  exact Erdos587.maxNotSqSum_le N

theorem extremal_zero : extremal 0 = 0 := Nat.eq_zero_of_le_zero (extremal_le_interval 0)

theorem extremal_mono : Monotone extremal := by
  intro M N hMN
  obtain ⟨A, hA, hfree, hcard⟩ := exists_extremizer M
  rw [← hcard]
  exact card_le_extremal (hA.trans (Finset.Icc_subset_Icc le_rfl hMN)) hfree

/-- Explicit cube-root lower bound, with no asymptotic assumptions. -/
theorem extremal_lower_bound (N : ℕ) (hN : 64 ≤ N) :
    (N : ℝ) ^ (1 / 3 : ℝ) / 4 ≤ (extremal N : ℝ) := by
  rw [extremal_eq_upstream]
  exact Erdos587.cube_root_div_four_le_maxNotSqSum N hN

/-- Absolute constants and a threshold; the bound applies to every finite set. -/
theorem uniform_polylog_upper_bound :
    ∃ O : ℕ, 0 < O ∧ ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ A ⊆ Finset.Icc 1 N, SquareSumFree A →
        (A.card : ℝ) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ) * Real.log N ^ O := by
  obtain ⟨O, hO, K, hK, N₀, hbound⟩ := Erdos587.upper_bound
  refine ⟨O, hO, K, hK, N₀, ?_⟩
  intro N hN A hA hfree
  have hcard : (A.card : ℝ) ≤ (extremal N : ℝ) := by
    exact_mod_cast card_le_extremal hA hfree
  rw [extremal_eq_upstream] at hcard
  exact hcard.trans (hbound N hN)

/-- The complete extremal asymptotic, in our original predicate. -/
theorem complete_extremal (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (N : ℝ) ^ (1 / 3 - ε) ≤ (extremal N : ℝ) ∧
        (extremal N : ℝ) ≤ (N : ℝ) ^ (1 / 3 + ε) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (Erdos587.eventually_power_bounds ε hε)
  refine ⟨N₀, ?_⟩
  intro N hN
  simpa only [extremal_eq_upstream] using hN₀ N hN

/-- Direct original-problem endpoint: witnesses below, every admissible set above. -/
theorem complete_problem (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∃ A ⊆ Finset.Icc 1 N, SquareSumFree A ∧
        (N : ℝ) ^ (1 / 3 - ε) ≤ (A.card : ℝ)) ∧
      (∀ A ⊆ Finset.Icc 1 N, SquareSumFree A →
        (A.card : ℝ) ≤ (N : ℝ) ^ (1 / 3 + ε)) := by
  obtain ⟨N₀, hN₀⟩ := complete_extremal ε hε
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hlower, hupper⟩ := hN₀ N hN
  constructor
  · obtain ⟨A, hA, hfree, hcard⟩ := exists_extremizer N
    exact ⟨A, hA, hfree, by simpa only [hcard] using hlower⟩
  · intro A hA hfree
    have hcard : (A.card : ℝ) ≤ (extremal N : ℝ) := by
      exact_mod_cast card_le_extremal hA hfree
    exact hcard.trans hupper

/-- A set larger than the upper threshold contains a nonempty square-sum subset. -/
theorem eventual_square_forcing (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ⊆ Finset.Icc 1 N,
      (N : ℝ) ^ (1 / 3 + ε) < (A.card : ℝ) →
        ∃ S ⊆ A, S.Nonempty ∧ ∃ x : ℕ, ∑ a ∈ S, a = x ^ 2 := by
  classical
  obtain ⟨N₀, hN₀⟩ := complete_problem ε hε
  refine ⟨N₀, ?_⟩
  intro N hN A hA hlarge
  have hnot : ¬ SquareSumFree A := by
    intro hfree
    exact (not_lt_of_ge ((hN₀ N hN).2 A hA hfree)) hlarge
  unfold SquareSumFree at hnot
  push Not at hnot
  exact hnot

end JSP000476
