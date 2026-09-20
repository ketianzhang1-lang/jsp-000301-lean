import JSP000728Complete

open Filter
open scoped Topology

/- Independent specification from the original relative-count question in
   Balogh--Liu--Sharifzadeh--Treglown, arXiv:1409.5661v1, Section 1.
   Equal summands are included. Maximality is by inclusion in all of [1,N]. -/
namespace Verify728

def SumFree (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y ≠ z

def Maximal (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ SumFree A ∧
    ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N → SumFree B → A ⊆ B → B = A

noncomputable def F (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter SumFree).card

noncomputable def M (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter (Maximal N)).card

theorem sumFree_iff (A : Finset ℕ) : SumFree A ↔ JSP000728.SumFree A := by
  constructor
  · intro h x hx y hy hxy
    exact h x hx y hy (x + y) hxy rfl
  · intro h x hx y hy z hz hxyz
    exact h x hx y hy (hxyz.symm ▸ hz)

theorem maximal_iff (N : ℕ) (A : Finset ℕ) :
    Maximal N A ↔ JSP000728.MaximalSumFree N A := by
  simp only [Maximal, JSP000728.MaximalSumFree, sumFree_iff]

theorem maximal_count (N : ℕ) : M N = (JSP000728.maximalSets N).card := by
  classical
  unfold M JSP000728.maximalSets
  congr 1
  ext A
  simp only [Finset.mem_filter, maximal_iff]

theorem all_count (N : ℕ) : F N = (JSP000728.allSumFreeSets N).card := by
  classical
  unfold F JSP000728.allSumFreeSets
  congr 1
  ext A
  simp only [Finset.mem_filter, sumFree_iff]

/- Explicit import bridges preserve the three original AuditComplete targets
   whose immutable source files are fetched dependencies rather than Git blobs
   in the submitted repository. The original audit checks their original names. -/
theorem upstream_littleO :
    (fun N : ℕ => (Erdos877.maximalSumFreeCount N : ℝ)) =o[atTop]
      (fun N : ℕ => Real.rpow 2 ((N : ℝ) / 2)) := Erdos877.erdos_877

theorem upstream_exponential :
    ∀ᶠ N : ℕ in atTop, (Erdos877.maximalSumFreeCount N : ℝ) ≤
      Real.rpow 2 (Erdos877.resolutionExponent * (N : ℝ)) :=
  Erdos877.erdos_877_exponential_bound

theorem upstream_exponent_lt_half : Erdos877.resolutionExponent < (1 / 2 : ℝ) :=
  Erdos877.resolutionExponent_lt_half

theorem intended :
    (∀ N : ℕ, 2 ^ (N / 4) ≤ M N) ∧
    ((fun N : ℕ => (M N : ℝ)) =o[atTop] (fun N : ℕ => (F N : ℝ))) ∧
    Tendsto (fun N : ℕ => (M N : ℝ) / (F N : ℝ)) atTop (𝓝 0) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      (M N : ℝ) ≤ (F N : ℝ) / Real.rpow 2 (δ * (N : ℝ))) := by
  simpa only [maximal_count, all_count] using
    And.intro JSP000728.jsp_000728.1
      (And.intro JSP000728.jsp_000728.2.1
        (And.intro JSP000728.maximal_to_all_ratio_tendsto_zero
          JSP000728.jsp_000728.2.2))

end Verify728
