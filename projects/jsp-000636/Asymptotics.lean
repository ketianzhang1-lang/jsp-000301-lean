import Thinning
import Mathlib.Analysis.SpecificLimits.Basic

/-!
We connect the exact-multiplicity wording of the Erdős–Trotter question to the
least threshold, and prove its sharp leading asymptotic n₀(r)/r → 2.
The underlying lower bound and label method are credited to Yixin He and
Quanyu Tang. This module does not claim their sharper logarithmic error term.
-/

namespace JSP000636
open Finset Filter
open scoped Topology

/-- The extremal number of occurring sizes using the original exact-r convention. -/
noncomputable def exactExtremal (n r : ℕ) : ℕ := by
  classical
  exact (univ.filter (fun F : Finset (Finset (Fin n)) =>
    Antichain F ∧ ExactMultiplicity r F)).sup (fun F => (sizes F).card)

/-- At-least-r and exactly-r conventions have the same extremal value. -/
theorem exactExtremal_eq (n r : ℕ) (hr : 0 < r) :
    exactExtremal n r = extremal n r := by
  classical
  apply Nat.le_antisymm
  · unfold exactExtremal
    apply Finset.sup_le
    intro F hF
    obtain ⟨ha,hm⟩ := (mem_filter.mp hF).2
    exact Finset.le_sup (f := fun F => (sizes F).card)
      (mem_filter.mpr ⟨mem_univ _,ha,fun A hA => (hm A hA).ge⟩)
  · unfold extremal
    apply Finset.sup_le
    intro F hF
    obtain ⟨ha,hm⟩ := (mem_filter.mp hF).2
    obtain ⟨G,_,hGa,hGe,hGs⟩ := thin_to_exact hr F ha hm
    rw [← hGs]
    exact Finset.le_sup (f := fun G => (sizes G).card)
      (mem_filter.mpr ⟨mem_univ _,hGa,hGe⟩)

/-- Exact-multiplicity eventual equality, with an explicit bound for every r ≥ 2. -/
theorem exactExtremal_eventually_eq (n r : ℕ) (hr : 2 ≤ r)
    (hn : 2*r+4*Nat.sqrt r+8 ≤ n) : exactExtremal n r = n-3 := by
  rw [exactExtremal_eq n r (by omega)]
  exact extremal_eventually_eq n r hr hn

/-- A total function agrees with the least threshold on the problem's domain.
The arbitrary value below r=2 has no effect on the asymptotic statement. -/
noncomputable def threshold (r : ℕ) : ℕ :=
  if hr : 2 ≤ r then leastThreshold r hr else 0

theorem threshold_eq (r : ℕ) (hr : 2 ≤ r) :
    threshold r = leastThreshold r hr := by simp [threshold,hr]

/-- The selected value really is the least threshold for the original convention. -/
theorem threshold_exact_spec (r : ℕ) (hr : 2 ≤ r) :
    (∀ n > threshold r, exactExtremal n r = n-3) ∧
    (∀ N, (∀ n > N, exactExtremal n r = n-3) → threshold r ≤ N) := by
  rw [threshold_eq r hr]
  constructor
  · intro n hn
    rw [exactExtremal_eq n r (by omega)]
    exact leastThreshold_spec r hr n hn
  · intro N hN
    apply leastThreshold_le r N hr
    intro n hn
    rw [← exactExtremal_eq n r (by omega)]
    exact hN n hn

theorem threshold_bounds (r : ℕ) (hr : 4 ≤ r) :
    2*r+2 ≤ threshold r ∧ threshold r ≤ 2*r+4*Nat.sqrt r+7 := by
  rw [threshold_eq r (by omega)]
  exact leastThreshold_bounds r hr

/-- A fully explicit relative-error estimate, uniform beyond a computable cutoff. -/
theorem threshold_relative_bound (m r : ℕ) (hm : 1 ≤ m)
    (hr : (8*m+8)^2 ≤ r) :
    2*r ≤ threshold r ∧ m*threshold r ≤ (2*m+1)*r := by
  have hs : 8*m+8 ≤ Nat.sqrt r := (Nat.le_sqrt').mpr hr
  have hr4 : 4 ≤ r := by nlinarith
  obtain ⟨hlo,hhi⟩ := threshold_bounds r hr4
  have hs2 := Nat.sqrt_le r
  have hprod : (4*m+1)*Nat.sqrt r ≤ Nat.sqrt r*Nat.sqrt r :=
    Nat.mul_le_mul_right _ (by omega)
  have herr : m*(4*Nat.sqrt r+7) ≤ r := by nlinarith
  constructor
  · omega
  · have := Nat.mul_le_mul_left m hhi
    nlinarith

/-- The relative error bound in the ordinary real-valued formulation. -/
theorem threshold_ratio_bound (m r : ℕ) (hm : 1 ≤ m)
    (hr : (8*m+8)^2 ≤ r) :
    2 ≤ (threshold r : ℝ)/r ∧ (threshold r : ℝ)/r ≤ 2+1/(m : ℝ) := by
  obtain ⟨hlo,hhi⟩ := threshold_relative_bound m r hm hr
  have hrpos : 0 < r := by nlinarith
  have hrr : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hmr : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  constructor
  · apply (le_div_iff₀ hrr).mpr
    exact_mod_cast hlo
  · apply (div_le_iff₀ hrr).mpr
    have hh : (m : ℝ)*(threshold r : ℝ) ≤ (2*(m : ℝ)+1)*(r : ℝ) := by
      exact_mod_cast hhi
    apply (mul_le_mul_iff_right₀ hmr).mp
    calc
      (m : ℝ)*(threshold r : ℝ) ≤ (2*(m : ℝ)+1)*r := hh
      _ = (m : ℝ)*((2+1/(m : ℝ))*r) := by field_simp

/-- Sharp leading asymptotic of the original least threshold. -/
theorem threshold_ratio_tendsto :
    Tendsto (fun r : ℕ => (threshold r : ℝ)/r) atTop (𝓝 (2 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  refine ⟨(8*(m+1)+8)^2,?_⟩
  intro r hr
  obtain ⟨hlo,hhi⟩ := threshold_ratio_bound (m+1) r (by omega) hr
  rw [Real.dist_eq,abs_of_nonneg (by linarith : 0 ≤ (threshold r : ℝ)/r-2)]
  have hm' : 1 / ((m+1 : ℕ) : ℝ) < ε := by simpa using hm
  linarith

/-- The full quantified extremal statement in the original exact-r wording. -/
theorem exact_threshold_estimate :
    ∀ r ≥ 2, ∃ N ≤ 2*r+4*Nat.sqrt r+7,
      ∀ n > N,
        (∃ F : Finset (Finset (Fin n)),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset (Fin n))) ∧
          ExactMultiplicity r F ∧ F.card = r*(n-3)) ∧
        (∀ F : Finset (Finset (Fin n)),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset (Fin n))) →
          ExactMultiplicity r F → F.card ≤ r*(n-3)) := by
  intro r hr
  refine ⟨2*r+4*Nat.sqrt r+7,le_rfl,?_⟩
  intro n hn
  constructor
  · obtain ⟨F,ha,he,_,hc⟩ := exact_attaining_family n r hr (by omega)
    exact ⟨F,(antichain_iff_isAntichain F).mp ha,he,hc⟩
  · exact fun F ha he => exact_multiplicity_card_le n r (by omega) hr F ha he

/-- Combined estimate endpoint: exact-multiplicity eventual equality,
its genuine least-threshold semantics, and sharp leading growth. -/
theorem jsp_000636_estimate :
    (∀ r ≥ 2, ∃ N ≤ 2*r+4*Nat.sqrt r+7,
      ∀ n > N, exactExtremal n r = n-3) ∧
    (∀ r ≥ 2,
      (∀ n > threshold r, exactExtremal n r = n-3) ∧
      (∀ N, (∀ n > N, exactExtremal n r = n-3) → threshold r ≤ N)) ∧
    (∀ r ≥ 4, 2*r+2 ≤ threshold r ∧ threshold r ≤ 2*r+4*Nat.sqrt r+7) ∧
    Tendsto (fun r : ℕ => (threshold r : ℝ)/r) atTop (𝓝 (2 : ℝ)) := by
  refine ⟨?_,threshold_exact_spec,threshold_bounds,threshold_ratio_tendsto⟩
  intro r hr
  refine ⟨2*r+4*Nat.sqrt r+7,le_rfl,?_⟩
  intro n hn
  exact exactExtremal_eventually_eq n r hr (by omega)

end JSP000636
