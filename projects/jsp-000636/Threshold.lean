import Construction

namespace JSP000636
open Finset

/-- A square-root sized pool contains enough incomparable pair labels. -/
theorem sqrt_pair_capacity (r k : ℕ) (hk : r+2*Nat.sqrt r+4 ≤ k) :
    k-3 ≤ (k-r).choose 2 := by
  have hm : 2*Nat.sqrt r+4 ≤ k-r := by omega
  have hm3 : k-r-3+3 = k-r := by omega
  have hm1 : k-r-1+1 = k-r := by omega
  have hkr : k-r+r = k := by omega
  have hk3 : k-3+3 = k := by omega
  have hp : (2*Nat.sqrt r+4)*(2*Nat.sqrt r+1) ≤ (k-r)*(k-r-3) :=
    Nat.mul_le_mul hm (by omega)
  have hs := Nat.lt_succ_sqrt' r
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simp only [Nat.succ_eq_add_one] at hs
  nlinarith

/-- For every sufficiently large n, an attaining family actually exists. -/
theorem attaining_family (n r : ℕ) (hr : 2 ≤ r)
    (hn : 2*r+4*Nat.sqrt r+8 ≤ n) :
    ∃ F : Finset (Finset (Fin n)),
      Antichain F ∧ Multiplicity r F ∧ (sizes F).card = n-3 := by
  let k := n/2
  have hnlo : 2*k ≤ n := by have := Nat.div_mul_le_self n 2; dsimp [k]; omega
  have hnhi : n ≤ 2*k+1 := by have := Nat.lt_mul_div_succ n (by decide : 0 < 2); dsimp [k]; omega
  have hk : r+2*Nat.sqrt r+4 ≤ k := by omega
  obtain ⟨H⟩ := pairLabel_half_exists n r k hr (by omega) hnlo (sqrt_pair_capacity r k hk)
  exact ⟨H.full,H.full_antichain hnlo,H.full_multiplicity,
    H.full_size_count hr (by omega) hnlo hnhi⟩

/-- Explicit eventual equality for the finite extremal function. -/
theorem extremal_eventually_eq (n r : ℕ) (hr : 2 ≤ r)
    (hn : 2*r+4*Nat.sqrt r+8 ≤ n) : extremal n r = n-3 := by
  classical
  apply Nat.le_antisymm
  · unfold extremal
    apply Finset.sup_le
    intro F hF
    obtain ⟨ha,hm⟩ := (mem_filter.mp hF).2
    exact size_count_le n r (by omega) hr F ha hm
  · obtain ⟨F,ha,hm,hcard⟩ := attaining_family n r hr hn
    have hmem : F ∈ univ.filter (fun F : Finset (Finset (Fin n)) =>
        Antichain F ∧ Multiplicity r F) := mem_filter.mpr ⟨mem_univ _,ha,hm⟩
    have hh := le_sup (f := fun F => (sizes F).card) hmem
    rw [hcard] at hh
    exact hh

/-- An explicit (non-optimal) upper threshold. -/
theorem threshold_upper_bound (r : ℕ) (hr : 2 ≤ r) :
    IsThreshold r (2*r+4*Nat.sqrt r+7) := by
  intro n hn
  exact extremal_eventually_eq n r hr (by omega)

theorem threshold_exists (r : ℕ) (hr : 2 ≤ r) : ∃ N, IsThreshold r N :=
  ⟨2*r+4*Nat.sqrt r+7, threshold_upper_bound r hr⟩

/-- The least threshold is defined only after its existence has been proved. -/
noncomputable def leastThreshold (r : ℕ) (hr : 2 ≤ r) : ℕ := by
  classical
  exact Nat.find (threshold_exists r hr)

theorem leastThreshold_spec (r : ℕ) (hr : 2 ≤ r) :
    IsThreshold r (leastThreshold r hr) := by
  classical
  exact Nat.find_spec (threshold_exists r hr)

theorem leastThreshold_le (r N : ℕ) (hr : 2 ≤ r) (hN : IsThreshold r N) :
    leastThreshold r hr ≤ N := by
  classical
  exact Nat.find_min' (threshold_exists r hr) hN

/-- Certified bounds for every r ≥ 4; the upper bound has a coarser asymptotic error than the paper's. -/
theorem leastThreshold_bounds (r : ℕ) (hr : 4 ≤ r) :
    2*r+2 ≤ leastThreshold r (by omega) ∧
    leastThreshold r (by omega) ≤ 2*r+4*Nat.sqrt r+7 := by
  constructor
  · exact threshold_lower_bound r _ hr (leastThreshold_spec r (by omega))
  · exact leastThreshold_le r _ (by omega) (threshold_upper_bound r (by omega))

end JSP000636
