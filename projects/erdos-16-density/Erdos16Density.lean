import Erdos16

/-!
# Erdős 16: the natural-density statement and the zero-exponent boundary

This supplement uses Chen's theorem as formalized in the pinned `Erdos16`
source. That source's predicate named `density_zero` means absence of an
infinite arithmetic progression. Here `NaturalDensityZero` is the actual
counting-function limit. The bridge is proved, not assumed.

The final theorem also allows exponent zero, matching Formal Conjectures'
statement. The two exceptional sets differ exactly at the integer 3.
-/

namespace Erdos16Density

open Filter
open scoped Topology

noncomputable section

/-- Natural density zero, with counting in `[0, n)`. -/
def NaturalDensityZero (S : Set ℕ) : Prop :=
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  Tendsto (fun n : ℕ => (Nat.count (· ∈ S) n : ℝ) / n) atTop (𝓝 0)

/-- The exact set in the Formal Conjectures statement: zero exponent is allowed. -/
def Exceptional : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p}

/-- An arithmetic progression contributes at least `n` terms below `m*n+a`. -/
theorem progression_count_lower {S : Set ℕ} {m a : ℕ} (hm : 0 < m)
    (hS : {x | ∃ k, x = m * k + a} ⊆ S) (n : ℕ) :
    letI : DecidablePred (· ∈ S) := Classical.decPred _
    n ≤ Nat.count (· ∈ S) (m * n + a) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let f : ℕ → ℕ := fun k => m * k + a
  have hf : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel hij)
  have hs : (Finset.range n).image f ⊆
      (Finset.range (m * n + a)).filter (· ∈ S) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_filter.mpr ⟨?_, hS ⟨k, rfl⟩⟩
    apply Finset.mem_range.mpr
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hk) hm) a
  simpa [Finset.card_image_of_injective _ hf] using Finset.card_le_card hs

/-- The actual density-zero condition implies the upstream no-progression predicate. -/
theorem no_progression_of_density_zero {S : Set ℕ} (hS : NaturalDensityZero S) :
    Erdos16.density_zero S := by
  classical
  intro m a hm hsub
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hevent := (tendsto_order.mp hS).2 (1 / (2 * (m : ℝ))) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let n := N + a + 1
  have hn : 0 < n := by dsimp [n]; omega
  have ha : a ≤ n := by dsimp [n]; omega
  have hnm : n ≤ m * n := by nlinarith
  have hNx : N ≤ m * n + a := by dsimp [n] at *; omega
  have hx : (0 : ℝ) < (m * n + a : ℕ) := by exact_mod_cast (by omega : 0 < m * n + a)
  have hsmall := (div_lt_div_iff₀ hx (by positivity : (0 : ℝ) < 2 * m)).mp (hN _ hNx)
  have hcount : (n : ℝ) ≤ Nat.count (· ∈ S) (m * n + a) := by
    exact_mod_cast progression_count_lower hm hsub n
  have hbound : m * n + a ≤ 2 * m * n := by nlinarith
  have hboundR : ((m * n + a : ℕ) : ℝ) ≤ 2 * (m : ℝ) * n := by exact_mod_cast hbound
  nlinarith

/-- Inserting one point cannot create an infinite arithmetic progression. -/
theorem no_progression_insert {S : Set ℕ} (hS : Erdos16.density_zero S) (b : ℕ) :
    Erdos16.density_zero (insert b S) := by
  intro m a hm hsub
  apply hS m (m * (b + 1) + a) hm
  rintro x ⟨k, rfl⟩
  have hx := hsub (show m * k + (m * (b + 1) + a) ∈
      {x | ∃ j, x = m * j + a} from ⟨k + (b + 1), by ring⟩)
  have hlarge : b < m * k + (m * (b + 1) + a) := by nlinarith
  exact (Set.mem_insert_iff.mp hx).resolve_left (by omega)

/-- Allowing the zero exponent removes exactly 3 from the upstream exceptional set. -/
theorem upstream_set_eq_insert : Erdos16.U = insert 3 Exceptional := by
  ext n
  constructor
  · intro hn
    by_cases hzero : ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p
    · obtain ⟨k, p, hp, heq⟩ := hzero
      have hk : k = 0 := by
        by_contra hk
        exact hn.2 ⟨p, k, hp, Nat.pos_of_ne_zero hk, by omega⟩
      subst k
      simp only [pow_zero] at heq
      have hp2 : p = 2 := by
        rcases hp.eq_two_or_odd' with h | h
        · exact h
        · obtain ⟨u, hu⟩ := hn.1
          obtain ⟨v, hv⟩ := h
          omega
      simp [heq, hp2]
    · exact Set.mem_insert_of_mem 3 ⟨hn.1, hzero⟩
  · intro hn
    rcases Set.mem_insert_iff.mp hn with rfl | hn
    · refine ⟨by decide, ?_⟩
      rintro ⟨p, k, hp, hk, heq⟩
      have hpow : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
             _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      have := hp.two_le
      omega
    · refine ⟨hn.1, ?_⟩
      rintro ⟨p, k, hp, _, heq⟩
      exact hn.2 ⟨k, p, hp, by omega⟩

/-- Chen's original positive-exponent conclusion with actual natural density. -/
theorem no_decomposition_positive_exponent :
    ¬ ∃ m a : ℕ, 0 < m ∧ ∃ W : Set ℕ,
      NaturalDensityZero W ∧ Erdos16.U = {x | ∃ k, x = m * k + a} ∪ W := by
  rintro ⟨m, a, hm, W, hW, heq⟩
  exact Erdos16.not_erdos_16 ⟨m, a, hm, W, no_progression_of_density_zero hW, heq⟩

/-- Full one-progression statement with nonnegative exponents and natural density zero. -/
theorem no_decomposition :
    ¬ ∃ A B : Set ℕ, Exceptional = A ∪ B ∧
      (∃ a d : ℕ, 0 < d ∧ A = {x | ∃ m : ℕ, x = a + m * d}) ∧
      NaturalDensityZero B := by
  rintro ⟨A, B, heq, ⟨a, d, hd, hA⟩, hB⟩
  apply Erdos16.not_erdos_16
  refine ⟨d, a, hd, insert 3 B, no_progression_insert (no_progression_of_density_zero hB) 3, ?_⟩
  rw [upstream_set_eq_insert, heq, hA]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · obtain ⟨k, hk⟩ := h
      exact Or.inl ⟨k, by simpa [Nat.add_comm, Nat.mul_comm] using hk⟩
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · obtain ⟨k, hk⟩ := h
      exact Or.inr (Or.inl ⟨k, by simpa [Nat.add_comm, Nat.mul_comm] using hk⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end
end Erdos16Density
