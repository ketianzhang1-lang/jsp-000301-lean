/-
Strict-gap supplement to the pinned Erdos1114 development by
Codex / GPT-5.6 Sol in plby/lean-proofs (8822f7ddef30fadbd92e1c6ab4ed897af356af5e).
Mathematical source: Elemer Balint (1960); see PROVENANCE.md.
This file supplies the strictness argument; the imported non-strict development
and its analytic infrastructure are prior work, not claimed here.
-/
import Erdos1114

open scoped BigOperators Topology
open Filter Set Polynomial
open Erdos1114

namespace JSP000925Strict

/-- Strict positivity follows from an explicit sum of five nonnegative terms,
with a strictly positive first term. -/
lemma strict_algebra {u z s t v : ℝ}
    (hu : 0 < u) (hz : 0 ≤ z) (hs : 0 < s)
    (hm : t ^ 2 ≤ s * v) (hc : s ^ 3 ≤ 4 * t) :
    0 < 4 * u * ((3 * t + 4 * z * v) * (Real.pi ^ 2 + 4 * z * s ^ 2) -
      4 * s * (s + 2 * z * t) ^ 2) := by
  have ht : 0 < t := by nlinarith [pow_pos hs 3]
  have hv : 0 ≤ v := by nlinarith [sq_nonneg t]
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpi0 : 0 < 3 * Real.pi ^ 2 - 16 := by linarith
  have hpi2 : 0 < Real.pi ^ 2 - 4 := by linarith
  have h0 : 0 < (3 * Real.pi ^ 2 - 16) * s * t := by positivity
  have h1 : 0 ≤ 4 * s * (4 * t - s ^ 3) := by positivity
  have h2 : 0 ≤ 4 * z * (Real.pi ^ 2 - 4) * s * v := by positivity
  have h3 : 0 ≤ 4 * z * (4 * (s * v - t ^ 2) + t * (4 * t - s ^ 3)) := by
    positivity
  have h4 : 0 ≤ 16 * z ^ 2 * s ^ 2 * (s * v - t ^ 2) := by positivity
  have hprod : 0 < s * ((3 * t + 4 * z * v) * (Real.pi ^ 2 + 4 * z * s ^ 2) -
      4 * s * (s + 2 * z * t) ^ 2) := by nlinarith only [h0, h1, h2, h3, h4]
  have hinner := (mul_pos_iff_of_pos_left hs).mp hprod
  exact mul_pos (mul_pos (by norm_num) hu) hinner

lemma phase_second_positive {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Ioo 0 (radius N)) : 0 < phaseDeriv2 N u := by
  have hclosed : u ∈ Icc 0 (radius N) := ⟨hu.1.le, hu.2.le⟩
  have h := strict_algebra hu.1 (sq_nonneg u)
    (moment_one_pos hN hclosed) (phase_moment_cauchy hN hclosed)
    (phase_moment_cubic hN hclosed)
  have hn : 0 < phaseRemainderDeriv2 N u * (Real.pi ^ 2 + phaseRemainder N u ^ 2) -
      2 * phaseRemainder N u * phaseRemainderDeriv N u ^ 2 := by
    unfold phaseRemainder phaseRemainderDeriv phaseRemainderDeriv2
    nlinarith only [h]
  unfold phaseDeriv2
  exact div_pos hn (sq_pos_of_pos (by positivity))

lemma phase_strict_convex {N : ℕ} (hN : 0 < N) :
    StrictConvexOn ℝ (Icc 0 (radius N)) (phase N) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc 0 (radius N)) (phase_continuousOn N)
  intro x hx
  have hx' : x ∈ Ioo 0 (radius N) := by simpa only [interior_Icc] using hx
  have hr : 0 < radius N := by unfold radius; positivity
  have hxfull : x ∈ Ioo (-radius N) (radius N) := ⟨by linarith [hx'.1], hx'.2⟩
  have heq : deriv (phase N) =ᶠ[𝓝 x] phaseDeriv N := by
    filter_upwards [isOpen_Ioo.mem_nhds hxfull] with y hy
    exact (phase_hasDerivAt hN hy).deriv
  have hsecond : HasDerivAt (deriv (phase N)) (phaseDeriv2 N x) x :=
    (phaseDeriv_hasDerivAt hN hxfull).congr_of_eventuallyEq heq
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, hsecond.deriv]
    using phase_second_positive hN hx'

/-- The predicate excludes the equal, mirror-image central pair of gaps. -/
def RightGapStrict (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i, i + 2 < N → N ≤ 2 * (i + 1) →
    b (i + 1) - b i < b (i + 2) - b (i + 1)

lemma reciprocal_slope_gap {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (h : (L - 1) / L < (R - 1) / R) : L < R := by
  rw [div_lt_div_iff₀ hL hR] at h
  nlinarith

/-- Strict convexity upgrades the canonical gap comparison, including the
central gap when the number of derivative roots is even. -/
theorem canonical_strict {N : ℕ} (hN : 0 < N) {b : ℕ → ℝ}
    (hb : ∀ k, k < N → b k ∈ Ioo (k : ℝ) ((k : ℝ) + 1))
    (hz : ∀ k, k < N → reciprocalSum N (b k) = 0) : RightGapStrict N b := by
  have hs := canonical_symmetry_of_reciprocal_zeros hb hz
  have hc : ∀ k, k < N → 1 / (b k - k) +
      (∑ n ∈ Finset.range (N - k), negTerm (b k - k) n) +
      (∑ n ∈ Finset.range k, posTerm (b k - k) n) = 0 := by
    intro k hk
    have h := hz k hk
    rw [show b k = (k : ℝ) + (b k - k) by ring,
      reciprocalSum_eq_decomposed hk] at h
    exact h
  intro i hi hright
  have hi0 : i < N := by omega
  have hi1 : i + 1 < N := by omega
  have hxy : centered N b i < centered N b (i + 1) := by
    unfold centered
    linarith [indexed_points_strictMono hb hi1 (by omega : i < i + 1)]
  have hyz : centered N b (i + 1) < centered N b (i + 2) := by
    unfold centered
    linarith [indexed_points_strictMono hb hi (by omega : i + 1 < i + 2)]
  have p1 := phase_centered_eq_of_right_or_center hi1 (by omega) hb hc hs
  have p2 := phase_centered_eq_of_right_or_center hi (by omega) hb hc hs
  have zm : centered N b (i + 2) ∈ Icc 0 (radius N) :=
    ⟨centered_nonneg_of_right hb hs hi (by omega), centered_le_radius hb hi⟩
  by_cases he : N = 2 * (i + 1)
  · have hy : 0 < centered N b (i + 1) := by
      have h := (hb (i + 1) hi1).1
      unfold centered radius
      rw [he]
      push_cast
      push_cast at h
      linarith
    have hsym := hs (i + 1) hi1
    rw [show N - 1 - (i + 1) = i by omega] at hsym
    have g := (phase_strict_convex hN).slope_strict_mono_adjacent
      (show (0 : ℝ) ∈ Icc 0 (radius N) from ⟨le_rfl, by unfold radius; positivity⟩)
      zm hy hyz
    rw [phase_zero, p1, p2] at g
    have hgap : b (i + 1) - b i = 2 * centered N b (i + 1) := by
      unfold centered radius
      linarith
    have hyEq : centered N b (i + 1) = b (i + 1) - (i + 1) := by
      unfold centered radius
      rw [he]
      push_cast
      ring
    have hd : centered N b (i + 2) - centered N b (i + 1) =
        b (i + 2) - b (i + 1) := by unfold centered; ring
    have hR : 0 < b (i + 2) - b (i + 1) := by
      linarith [indexed_points_strictMono hb hi (by omega : i + 1 < i + 2)]
    rw [hd, hyEq] at g
    have hL : 0 < b (i + 1) - (i + 1) := by rwa [hyEq] at hy
    norm_num [Nat.cast_add] at g
    rw [div_lt_div_iff₀ hL hR] at g
    rw [hgap, hyEq]
    nlinarith
  · have hr : N ≤ 2 * i + 1 := by omega
    have xm : centered N b i ∈ Icc 0 (radius N) :=
      ⟨centered_nonneg_of_right hb hs hi0 hr, centered_le_radius hb hi0⟩
    have p0 := phase_centered_eq_of_right_or_center hi0 hr hb hc hs
    have g := (phase_strict_convex hN).slope_strict_mono_adjacent xm zm hxy hyz
    rw [p0, p1, p2] at g
    have d0 : centered N b (i + 1) - centered N b i = b (i + 1) - b i := by
      unfold centered; ring
    have d1 : centered N b (i + 2) - centered N b (i + 1) =
        b (i + 2) - b (i + 1) := by unfold centered; ring
    rw [d0, d1] at g
    have hL : 0 < b (i + 1) - b i := by
      linarith [indexed_points_strictMono hb hi1 (by omega : i < i + 1)]
    have hR : 0 < b (i + 2) - b (i + 1) := by
      linarith [indexed_points_strictMono hb hi (by omega : i + 1 < i + 2)]
    apply reciprocal_slope_gap hL hR
    convert g using 1 <;> push_cast <;> congr 1 <;> ring

/-- Strict affine gap theorem for the actual polynomial derivative. -/
theorem strict_gap_theorem {N : ℕ} (hN : 0 < N) {a d : ℝ} (hd : 0 < d)
    {f : ℝ[X]} {b : ℕ → ℝ} (hf : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j, j ≤ N → eval (a + d * j) f = 0)
    (hb : ∀ k, k < N → b k ∈ Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : ∀ k, k < N → eval (b k) f.derivative = 0) :
    RightGapStrict N b ∧ GapSymmetric N b := by
  have hfct := eq_progression_factorization hd hf hdegree hroots
  have hlc := leadingCoeff_ne_zero.mpr hf
  have hg := canonical_strict hN
    (fun k hk => normalizePoint_mem_interval hd (hb k hk))
    (fun k hk => normalized_reciprocalSum_eq_zero hd hlc hfct (hb k hk) (hderiv k hk))
  refine ⟨?_, (erdos_1114 hN hd hf hdegree hroots hb hderiv).2⟩
  intro i hi hr
  have h := hg i hi hr
  change (b (i + 1) - a) / d - (b i - a) / d <
    (b (i + 2) - a) / d - (b (i + 1) - a) / d at h
  have heq (x y : ℝ) : (x - a) / d - (y - a) / d = (x - y) / d := by ring
  simp only [heq, div_lt_div_iff_of_pos_right hd] at h
  exact h


/-- Rolle's theorem constructs the critical point in each open root interval. -/
lemma interval_critical_exists {N k : ℕ} {a d : ℝ} (hd : 0 < d) {f : ℝ[X]}
    (hr : ∀ j, j ≤ N → eval (a + d * j) f = 0) (hk : k < N) :
    ∃ x ∈ Ioo (a + d * k) (a + d * (k + 1)), eval x f.derivative = 0 := by
  have he : eval (a + d * k) f = eval (a + d * (k + 1)) f := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (hr k (by omega)).trans (hr (k + 1) (by omega)).symm
  have hab : a + d * (k : ℝ) < a + d * (k + 1) := by nlinarith
  obtain ⟨x, hx, hdx⟩ := exists_deriv_eq_zero hab f.continuousOn he
  exact ⟨x, hx, by simpa only [f.deriv] using hdx⟩

/-- Uniqueness is inherited from strict decrease of the logarithmic derivative
on each interval and is transferred back through the affine normalization. -/
lemma interval_critical_unique {N k : ℕ} {a d : ℝ} (hd : 0 < d) {f : ℝ[X]}
    (hf : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hr : ∀ j, j ≤ N → eval (a + d * j) f = 0) {x y : ℝ}
    (hx : x ∈ Ioo (a + d * k) (a + d * (k + 1)))
    (hy : y ∈ Ioo (a + d * k) (a + d * (k + 1)))
    (hdx : eval x f.derivative = 0) (hdy : eval y f.derivative = 0) : x = y := by
  have hfactor := eq_progression_factorization hd hf hdegree hr
  have hlc := leadingCoeff_ne_zero.mpr hf
  have hzx := normalized_reciprocalSum_eq_zero (b := fun _ => x) hd hlc hfactor hx hdx
  have hzy := normalized_reciprocalSum_eq_zero (b := fun _ => y) hd hlc hfactor hy hdy
  have hn := reciprocalSum_injective_on_interval
    (normalizePoint_mem_interval (b := fun _ => x) hd hx)
    (normalizePoint_mem_interval (b := fun _ => y) hd hy) (hzx.trans hzy.symm)
  dsimp [normalizePoint] at hn
  have := (div_left_inj' hd.ne').mp hn
  linarith

/-- Self-contained existence statement: there is a unique derivative zero in
each successive root interval, with strictly increasing right-half gaps and
mirror-symmetric gaps. No critical-point selector is assumed. -/
theorem exists_unique_strict_gaps {N : ℕ} (hN : 0 < N) {a d : ℝ} (hd : 0 < d)
    {f : ℝ[X]} (hf : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j, j ≤ N → eval (a + d * j) f = 0) :
    ∃ b : ℕ → ℝ,
      (∀ k, k < N → b k ∈ Ioo (a + d * k) (a + d * (k + 1))) ∧
      (∀ k, k < N → eval (b k) f.derivative = 0) ∧
      (∀ k, k < N → ∀ x ∈ Ioo (a + d * k) (a + d * (k + 1)),
        eval x f.derivative = 0 → x = b k) ∧
      RightGapStrict N b ∧ GapSymmetric N b := by
  classical
  have hex : ∀ k : ℕ, ∃ x : ℝ, k < N →
      x ∈ Ioo (a + d * k) (a + d * (k + 1)) ∧ eval x f.derivative = 0 := by
    intro k
    by_cases hk : k < N
    · obtain ⟨x, hx, hd⟩ := interval_critical_exists hd hroots hk
      exact ⟨x, fun _ => ⟨hx, hd⟩⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose b hb using hex
  have hint := fun k hk => (hb k hk).1
  have hderiv := fun k hk => (hb k hk).2
  refine ⟨b, hint, hderiv, ?_, strict_gap_theorem hN hd hf hdegree hroots hint hderiv⟩
  intro k hk x hx hdx
  exact interval_critical_unique hd hf hdegree hroots hx (hint k hk) hdx (hderiv k hk)

#print axioms strict_gap_theorem
#print axioms exists_unique_strict_gaps
end JSP000925Strict
