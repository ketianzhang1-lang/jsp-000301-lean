/-
Copyright 2026. Licensed under the Apache License, Version 2.0.

JSP-000295 / Erdos 357: the known lower bound with leading constant two.
The definitions HasDistinctSums and f match the Apache-2.0 Formal Conjectures
statement at commit 40e7c98697de6f66b8cbdbf641749ab39ed9c152.
That statement attributes the asymptotic bound to Desmond Weisenberg.
The elementary proof below was independently written with OpenAI ChatGPT
assistance. It does not settle whether f(n) = o(n), or its exact growth rate.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace JSP000295
open Finset

/-- The sum of a nonempty interval in a consecutive-integer sequence. -/
def blockSum (A : ℤ) (u v : ℕ) : ℤ := ∑ i ∈ Ico u v, (A + i)

theorem twice_blockSum (A : ℤ) {u v : ℕ} (huv : u ≤ v) :
    2 * blockSum A u v = (v - u : ℤ) * (2 * A + u + v - 1) := by
  induction v, huv using Nat.le_induction with
  | base => simp [blockSum]
  | succ v hv ih =>
    rw [blockSum, sum_Ico_succ_top hv]
    change 2 * (blockSum A u v + (A + v)) = _
    push_cast
    nlinarith

/-- The explicit sequence has length `2*t+1` and ends at `(t+1)^2`. -/
def entry (t : ℕ) (i : Fin (2*t+1)) : ℤ := (t : ℤ)^2 + 1 + i.val

theorem block_length_lt (t : ℕ) {u v x y : ℕ}
    (huv : u < v) (hv : v ≤ 2*t+1) (hxy : x < y)
    (hlen : v-u < y-x) :
    blockSum ((t : ℤ)^2+1) u v < blockSum ((t : ℤ)^2+1) x y := by
  have h1 := twice_blockSum ((t : ℤ)^2+1) huv.le
  have h2 := twice_blockSum ((t : ℤ)^2+1) hxy.le
  let r : ℤ := v-u
  let s : ℤ := y-x
  have hr : 0 < r := by dsimp [r]; omega
  have hrs : r+1 ≤ s := by dsimp [r,s]; omega
  have hv' : (v : ℤ) ≤ 2*t+1 := by exact_mod_cast hv
  have hu' : (0 : ℤ) ≤ u := by positivity
  have hx' : (0 : ℤ) ≤ x := by positivity
  have hmax : 2 * blockSum ((t : ℤ)^2+1) u v ≤
      r * (2*((t : ℤ)^2+1) + 4*t+1-r) := by
    rw [h1]
    dsimp [r]
    nlinarith [mul_nonneg hr.le (show (0 : ℤ) ≤ 2*t+1-v by omega)]
  have hmin : s * (2*((t : ℤ)^2+1) + s-1) ≤
      2 * blockSum ((t : ℤ)^2+1) x y := by
    rw [h2]
    dsimp [s]
    nlinarith [mul_nonneg (show 0 ≤ s by omega) hx']
  have hincrease : (r+1) * (2*((t : ℤ)^2+1)+r) ≤
      s * (2*((t : ℤ)^2+1)+s-1) := by
    nlinarith [mul_nonneg (show 0 ≤ s-r-1 by omega)
      (show 0 ≤ 2*((t : ℤ)^2+1)+s+r by nlinarith [sq_nonneg (t : ℤ)])]
  have hgap : r * (2*((t : ℤ)^2+1)+4*t+1-r) <
      (r+1) * (2*((t : ℤ)^2+1)+r) := by
    nlinarith [sq_nonneg ((t : ℤ)-r)]
  omega

theorem blocks_injective (t : ℕ) {u v x y : ℕ}
    (huv : u < v) (hv : v ≤ 2*t+1) (hxy : x < y) (hy : y ≤ 2*t+1)
    (hsum : blockSum ((t : ℤ)^2+1) u v = blockSum ((t : ℤ)^2+1) x y) :
    u = x ∧ v = y := by
  have hlen : v-u = y-x := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact (ne_of_lt (block_length_lt t huv hv hxy h)) hsum
    · exact (ne_of_lt (block_length_lt t hxy hy huv h)) hsum.symm
  have hlen' : (v : ℤ)-u = y-x := by omega
  have h1 := twice_blockSum ((t : ℤ)^2+1) huv.le
  have h2 := twice_blockSum ((t : ℤ)^2+1) hxy.le
  have hcancel : (u : ℤ)+v = x+y := by
    rw [hsum, hlen'] at h1
    have : (y-x : ℤ) * (2*((t : ℤ)^2+1)+u+v-1) =
        (y-x) * (2*((t : ℤ)^2+1)+x+y-1) := h1.symm.trans h2
    have hz : (y-x : ℤ) ≠ 0 := by omega
    have := mul_left_cancel₀ hz this
    omega
  omega

/-- This is the interval-set definition used by the Formal Conjectures statement. -/
def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ i ∈ J, a i)

theorem connected_eq_Icc {k : ℕ} (J : Finset (Fin k))
    (hJ : (J : Set (Fin k)).OrdConnected) (hne : J.Nonempty) :
    J = Icc (J.min' hne) (J.max' hne) := by
  ext i
  constructor
  · intro hi
    exact mem_Icc.mpr ⟨min'_le J i hi, le_max' J i hi⟩
  · intro hi
    exact hJ.out (min'_mem J hne) (max'_mem J hne) (mem_Icc.mp hi)

theorem sum_fin_Icc {k : ℕ} (A : ℤ) (u v : Fin k) :
    (∑ i ∈ Icc u v, (A + i.val : ℤ)) = blockSum A u.val (v.val+1) := by
  have h := sum_map (Icc u v) Fin.valEmbedding (fun i : ℕ => (A+i : ℤ))
  rw [Fin.map_valEmbedding_Icc] at h
  have heq : Ico u.val (v.val+1) = Icc u.val v.val := by
    ext i
    simp only [mem_Ico, mem_Icc]
    omega
  simpa [blockSum, heq] using h.symm

theorem entry_pos (t : ℕ) (i : Fin (2*t+1)) : 0 < entry t i := by
  dsimp [entry]
  positivity

theorem entry_hasDistinctSums (t : ℕ) : HasDistinctSums (entry t) := by
  intro J hJ K hK hsum
  change (J : Set (Fin (2*t+1))).OrdConnected at hJ
  change (K : Set (Fin (2*t+1))).OrdConnected at hK
  by_cases hJe : J = ∅
  · subst J
    by_contra hKe
    have hpos := sum_pos (fun i (_ : i ∈ K) => entry_pos t i)
      (nonempty_iff_ne_empty.mpr (Ne.symm hKe))
    simp only [sum_empty] at hsum
    change (0 : ℤ) = ∑ i ∈ K, entry t i at hsum
    omega
  by_cases hKe : K = ∅
  · subst K
    have hpos := sum_pos (fun i (_ : i ∈ J) => entry_pos t i) (nonempty_iff_ne_empty.mpr hJe)
    simp only [sum_empty] at hsum
    omega
  have hnJ := nonempty_iff_ne_empty.mpr hJe
  have hnK := nonempty_iff_ne_empty.mpr hKe
  have hformJ := connected_eq_Icc J hJ hnJ
  have hformK := connected_eq_Icc K hK hnK
  have hsum' : blockSum ((t : ℤ)^2+1) (J.min' hnJ).val ((J.max' hnJ).val+1) =
      blockSum ((t : ℤ)^2+1) (K.min' hnK).val ((K.max' hnK).val+1) := by
    rw [← sum_fin_Icc, ← sum_fin_Icc, ← hformJ, ← hformK]
    exact hsum
  have hJle := min'_le J (J.max' hnJ) (max'_mem J hnJ)
  have hKle := min'_le K (K.max' hnK) (max'_mem K hnK)
  have hJbound := (J.max' hnJ).isLt
  have hKbound := (K.max' hnK).isLt
  have heq := blocks_injective t (show (J.min' hnJ).val < (J.max' hnJ).val+1 by omega)
    (show (J.max' hnJ).val+1 ≤ 2*t+1 by omega)
    (show (K.min' hnK).val < (K.max' hnK).val+1 by omega)
    (show (K.max' hnK).val+1 ≤ 2*t+1 by omega) hsum'
  have hmin : J.min' hnJ = K.min' hnK := Fin.ext heq.1
  have hmax : J.max' hnJ = K.max' hnK := Fin.ext (by omega)
  rw [hformJ, hformK, hmin, hmax]

/-- The same extremal function as in the cited Formal Conjectures statement. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

theorem entry_strictMono (t : ℕ) : StrictMono (entry t) := by
  intro i j hij
  dsimp [entry]
  have : (i.val : ℤ) < j.val := by exact_mod_cast (show i.val < j.val from hij)
  omega

theorem entry_bounds (t : ℕ) :
    Set.range (entry t) ⊆ Set.Icc 1 ((t+1)^2 : ℕ) := by
  rintro _ ⟨i, rfl⟩
  have hi := i.isLt
  have hnonneg : (0 : ℤ) ≤ i.val := by positivity
  dsimp [entry]
  constructor
  · nlinarith [sq_nonneg (t : ℤ)]
  · nlinarith

theorem admissible_length_le {n k : ℕ} {a : Fin k → ℤ}
    (hb : Set.range a ⊆ Set.Icc 1 n) (ha : StrictMono a) : k ≤ n := by
  have hm : Set.MapsTo a (univ : Finset (Fin k)) (Icc (1 : ℤ) n) := by
    intro i _
    exact mem_Icc.mpr (hb ⟨i,rfl⟩)
  have hc := card_le_card_of_injOn a hm ha.injective.injOn
  simpa using hc

theorem admissible_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ a : Fin k → ℤ,
      Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a} := by
  refine ⟨n, ?_⟩
  rintro k ⟨a,hb,ha,_⟩
  exact admissible_length_le hb ha

/-- A whole family of witnesses, rather than a finite enumeration. -/
theorem lower_bound_of_square_le {t n : ℕ} (hn : (t+1)^2 ≤ n) :
    2*t+1 ≤ f n := by
  apply le_csSup (admissible_bddAbove n)
  refine ⟨entry t, ?_, entry_strictMono t, entry_hasDistinctSums t⟩
  intro x hx
  have hb := entry_bounds t hx
  exact ⟨hb.1, hb.2.trans (by exact_mod_cast hn)⟩

/-- The explicit all-n lower bound underlying the known asymptotic constant two. -/
theorem lower_bound (n : ℕ) : 2 * n.sqrt - 1 ≤ f n := by
  by_cases hn : n = 0
  · subst n; simp
  have hp : 0 < n.sqrt := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
  have ht : n.sqrt-1+1 = n.sqrt := by omega
  have hsq : (n.sqrt-1+1)^2 ≤ n := by
    rw [ht, pow_two]
    exact Nat.sqrt_le n
  have := lower_bound_of_square_le hsq
  omega

/-- A real-valued version with an explicit bounded error term. -/
theorem real_lower_bound (n : ℕ) : 2 * Real.sqrt n - 3 ≤ (f n : ℝ) := by
  have hs : Real.sqrt n < (n.sqrt : ℝ)+1 := by
    apply (Real.sqrt_lt (by positivity) (by positivity)).mpr
    have h := Nat.lt_succ_sqrt n
    exact_mod_cast (show n < (n.sqrt+1)^2 by simpa [pow_two] using h)
  have hb : (2 : ℝ) * n.sqrt - 1 ≤ f n := by
    have h := lower_bound n
    by_cases hp : 0 < n.sqrt
    · exact_mod_cast (show (2*n.sqrt : ℤ)-1 ≤ f n by omega)
    · have hz : n.sqrt = 0 := by omega
      simp only [hz, Nat.cast_zero, mul_zero, zero_sub]
      linarith [show (0 : ℝ) ≤ (f n : ℝ) by positivity]
  linarith

open Filter Asymptotics
open scoped Topology

/-- Exact shape of the known Weisenberg lower-bound statement. -/
theorem weisenberg : ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (2 + o n) * Real.sqrt n ≤ f n := by
  refine ⟨fun n => -3 / Real.sqrt n, ?_, ?_⟩
  · apply (isLittleO_one_iff ℝ).mpr
    exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop (-3)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have heq : (2 + -3 / Real.sqrt n) * Real.sqrt n = 2 * Real.sqrt n - 3 := by
      field_simp
      ring
    rw [heq]
    exact real_lower_bound n

end JSP000295
