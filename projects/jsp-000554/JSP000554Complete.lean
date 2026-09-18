/-
Copyright 2026. Released under the Apache 2.0 license.
Formalization contribution: ketianzhang1-lang, with OpenAI ChatGPT assistance.

We connect our exact finite residue classification to the attributed complete
Gafni--Tao density-one formalization in ErdosProblems.Erdos682. The imported
analytic proof is by Codex / GPT-5.6 Sol, distributed in plby/lean-proofs.
-/
import JSP000554
import ErdosProblems.Erdos682

open Filter
open scoped Topology

namespace JSP000554

/-- The actual consecutive-prime indices classified by our `BadGap` predicate. -/
def badGapIndices : Set ℕ :=
  {n | BadGap (Erdos682.nthPrime n) (Erdos682.gapLength n)}

/-- The complementary set of prime-gap indices. -/
def goodGapIndices : Set ℕ := badGapIndicesᶜ

/-- Reconstruct the upper endpoint, including the initial gap from 2 to 3. -/
theorem lower_add_gap (n : ℕ) :
    Erdos682.nthPrime n + Erdos682.gapLength n = Erdos682.nthPrime (n + 1) := by
  exact Nat.add_sub_of_le (Erdos682.nthPrime_lt_succ n).le

/-- Our endpoint-based definition agrees with the original indexed exception. -/
theorem badGap_iff_exceptional (n : ℕ) :
    BadGap (Erdos682.nthPrime n) (Erdos682.gapLength n) ↔
      Erdos682.ExceptionalGap n := by
  rw [BadGap, lower_add_gap, Erdos682.exceptionalGap_iff]
  constructor
  · exact fun h => h.2.2.2
  · intro h
    exact ⟨Erdos682.nthPrime_prime n, Erdos682.nthPrime_prime (n + 1),
      Erdos682.no_prime_between_nthPrime n, h⟩

theorem badGapIndices_eq : badGapIndices = Erdos682.exceptionalGapIndices := by
  ext n
  exact badGap_iff_exceptional n

/-- Good indices express existence of an actual interior rough integer. -/
theorem mem_goodGapIndices_iff (n : ℕ) :
    n ∈ goodGapIndices ↔ ∃ m : ℕ,
      Erdos682.nthPrime n < m ∧ m < Erdos682.nthPrime (n + 1) ∧
        Erdos682.gapLength n ≤ m.minFac := by
  change (¬ BadGap (Erdos682.nthPrime n) (Erdos682.gapLength n)) ↔ _
  rw [badGap_iff_exceptional]
  exact not_not

theorem goodGapIndices_eq : goodGapIndices = Erdos682.goodGapIndices := by
  ext n
  exact mem_goodGapIndices_iff n

/-- The complete zero-density conclusion in our original predicate. -/
theorem badGapIndices_density_zero : badGapIndices.HasDensity 0 := by
  rw [badGapIndices_eq]
  exact Erdos682.exceptionalGapIndices_density_zero

/-- The complete original density-one conclusion. -/
theorem goodGapIndices_density_one : goodGapIndices.HasDensity 1 := by
  rw [goodGapIndices_eq]
  exact Erdos682.erdos_682

/-- Density as an explicit ratio over the first N consecutive-prime gaps. -/
theorem badGap_count_ratio_tendsto :
    Tendsto (fun N : ℕ => (Erdos682.prefixCount badGapIndices N : ℝ) / N)
      atTop (𝓝 0) := by
  simpa only [Set.HasDensity, Erdos682.partialDensity_eq_prefixCount_ratio] using
    badGapIndices_density_zero

theorem goodGap_count_ratio_tendsto :
    Tendsto (fun N : ℕ => (Erdos682.prefixCount goodGapIndices N : ℝ) / N)
      atTop (𝓝 1) := by
  simpa only [Set.HasDensity, Erdos682.partialDensity_eq_prefixCount_ratio] using
    goodGapIndices_density_one

/-- Apply our exact residue classifier to every indexed gap of length at least 2.
Endpoint primality is a theorem of prime enumeration, not an added hypothesis. -/
theorem exceptional_iff_residue (n : ℕ) (hh : 2 ≤ Erdos682.gapLength n) :
    Erdos682.ExceptionalGap n ↔
      Erdos682.gapLength n ≤ Erdos682.nthPrime n ∧
      Erdos682.nthPrime n % primorial (Erdos682.gapLength n) ∈
        omegaSet (Erdos682.gapLength n) := by
  rw [← badGap_iff_exceptional, badGap_iff_residue_all hh, lower_add_gap]
  simp only [Erdos682.nthPrime_prime, true_and]

/-- Our exact finite residue classes sit inside a zero-density exceptional set. -/
def residueExceptionIndices : Set ℕ :=
  {n | 2 ≤ Erdos682.gapLength n ∧
    Erdos682.gapLength n ≤ Erdos682.nthPrime n ∧
    Erdos682.nthPrime n % primorial (Erdos682.gapLength n) ∈
      omegaSet (Erdos682.gapLength n)}

theorem mem_residueExceptionIndices_iff (n : ℕ) :
    n ∈ residueExceptionIndices ↔
      2 ≤ Erdos682.gapLength n ∧ n ∈ badGapIndices := by
  change (2 ≤ Erdos682.gapLength n ∧ _) ↔ _
  apply and_congr_right
  intro hh
  exact (exceptional_iff_residue n hh).symm.trans (badGap_iff_exceptional n).symm

/-- The full density statement together with our all-gap residue equivalence.
No unproved analytic hypothesis is an argument of this theorem. -/
theorem jsp_000554 :
    {n : ℕ | ∃ m : ℕ,
      Erdos682.nthPrime n < m ∧ m < Erdos682.nthPrime (n + 1) ∧
        Erdos682.nthPrime (n + 1) - Erdos682.nthPrime n ≤ m.minFac}.HasDensity 1 ∧
    (∀ p h : ℕ, 2 ≤ h → (BadGap p h ↔
      h ≤ p ∧ p.Prime ∧ (p + h).Prime ∧ p % primorial h ∈ omegaSet h)) := by
  exact ⟨Erdos682.erdos_682, fun _ _ hh => badGap_iff_residue_all hh⟩

end JSP000554
