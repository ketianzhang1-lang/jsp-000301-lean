/-
Copyright 2026. Prepared for Ketian Zhang with OpenAI ChatGPT assistance.
Licensed under the Apache License, Version 2.0.
Formalization of the established Erdos-Rosenfeld bound; the general conjecture remains open.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option maxRecDepth 2000
namespace JSP000737
open Finset

/-- Integer points in a real interval of length `B` number at most `1+B`. -/
theorem card_le_length (s : Finset ℕ) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hs : ∀ a ∈ s, L ≤ (a : ℝ) ∧ (a : ℝ) ≤ L + B) :
    (s.card : ℝ) ≤ 1 + B := by
  have hsub : s ⊆ Icc ⌈L⌉₊ ⌊L+B⌋₊ := by
    intro a ha
    exact mem_Icc.mpr ⟨Nat.ceil_le.mpr (hs a ha).1, Nat.le_floor (hs a ha).2⟩
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  by_cases h : ⌈L⌉₊ ≤ ⌊L+B⌋₊ + 1
  · have hcast : (s.card : ℝ) ≤ (⌊L+B⌋₊ : ℝ) + 1 - ⌈L⌉₊ := by
      exact_mod_cast hc
    have hf := Nat.floor_le (show 0 ≤ L+B by linarith)
    have he := Nat.le_ceil L
    linarith
  · have : s.card = 0 := by omega
    simp only [this, Nat.cast_zero]
    linarith

/-- The sum of a factor pair determines its larger member. -/
theorem factor_sum_injective {n : ℕ} {r : ℝ} (hr : 0 < r) (hr2 : r^2 = (n : ℝ)) :
    Set.InjOn (fun d : ℕ => d + n / d)
      {d | d ∣ n ∧ r ≤ (d : ℝ)} := by
  intro a ha b hb hab
  have haR := ha.2
  have hbR := hb.2
  have hp : (a : ℝ) * (n / a : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' ha.1
  have hq : (b : ℝ) * (n / b : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hb.1
  have he : (a : ℝ) + (n / a : ℕ) = (b : ℝ) + (n / b : ℕ) := by
    exact_mod_cast hab
  have hroot : ((a : ℝ) - b) * ((a : ℝ) - (n / b : ℕ)) = 0 := by
    nlinarith only [hp, hq, he]
  rcases mul_eq_zero.mp hroot with h | h
  · exact_mod_cast (sub_eq_zero.mp h)
  · have hcross : (a : ℝ) * b = r^2 := by
      rw [sub_eq_zero.mp h, mul_comm]
      exact hq.trans hr2.symm
    have har : (a : ℝ) = r := by
      nlinarith only [haR, hbR, hr, hcross,
        mul_nonneg (sub_nonneg.mpr haR) (sub_nonneg.mpr hbR)]
    have hbr : (b : ℝ) = r := by nlinarith only [har, hcross, hr]
    exact_mod_cast (har.trans hbr.symm)

/-- Factor-pair sums fit into an interval of length `C²`. -/
theorem factor_sum_bounds {n d : ℕ} {r u C : ℝ}
    (hr : 0 < r) (hr2 : r^2 = (n : ℝ)) (hu : u^2 = r)
    (hC : 0 ≤ C) (hu0 : 0 ≤ u) (hd : d ∣ n)
    (hlo : r ≤ (d : ℝ)) (hhi : (d : ℝ) ≤ r + C*u) :
    2*r ≤ (d + n/d : ℕ) ∧ (d + n/d : ℕ) ≤ 2*r+C^2 := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le hr hlo
  have hp : (d : ℝ) * (n/d : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hsq : ((d : ℝ) - r)^2 ≤ (C*u)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ C*u-((d : ℝ)-r) by linarith)
      (show 0 ≤ C*u+((d : ℝ)-r) by positivity)]
  have hid : (d : ℝ) * ((d : ℝ) + (n/d : ℕ) - 2*r) = ((d : ℝ)-r)^2 := by
    nlinarith
  have hbase : 2*r ≤ (d : ℝ) + (n/d : ℕ) := by
    nlinarith [sq_nonneg ((d : ℝ)-r)]
  have hupp : (d : ℝ) + (n/d : ℕ) ≤ 2*r+C^2 := by
    have hc2 : 0 ≤ C^2 := sq_nonneg C
    have hmul := mul_le_mul_of_nonneg_left hlo hc2
    have hid2 : (C*u)^2 = C^2*r := by rw [mul_pow, hu]
    nlinarith
  simpa only [Nat.cast_add] using And.intro hbase hupp

/-- A nonasymptotic form of the Erdős–Rosenfeld short-interval bound. -/
theorem short_interval_bound (n : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let S := (Nat.divisors n).filter (fun d : ℕ =>
      (n : ℝ) ^ (1/2 : ℝ) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ) + C * (n : ℝ) ^ (1/4 : ℝ))
    (S.card : ℝ) ≤ 1+C^2 := by
  classical
  dsimp only
  by_cases hn : n = 0
  · simp only [hn, Nat.divisors_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let r : ℝ := (n : ℝ) ^ (1/2 : ℝ)
  let u : ℝ := (n : ℝ) ^ (1/4 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hn0 _
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0.le _
  have hr2 : r^2 = (n : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hu : u^2 = r := by
    dsimp [u, r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  let S := (Nat.divisors n).filter (fun d : ℕ =>
    r ≤ (d : ℝ) ∧ (d : ℝ) ≤ r+C*u)
  let T := S.image (fun d => d+n/d)
  have hmem (d : ℕ) (hd : d ∈ S) : d ∣ n ∧ r ≤ (d : ℝ) ∧ (d : ℝ) ≤ r+C*u := by
    obtain ⟨hdn, hlo, hhi⟩ := mem_filter.mp hd
    exact ⟨(Nat.mem_divisors.mp hdn).1, hlo, hhi⟩
  have hinj : Set.InjOn (fun d : ℕ => d+n/d) (↑S : Set ℕ) := by
    intro a ha b hb hab
    exact factor_sum_injective hr hr2 ⟨(hmem a ha).1, (hmem a ha).2.1⟩
      ⟨(hmem b hb).1, (hmem b hb).2.1⟩ hab
  have hcard : T.card = S.card := card_image_iff.mpr hinj
  have hbound : (T.card : ℝ) ≤ 1+C^2 := by
    apply card_le_length T (2*r) (C^2) (by positivity) (sq_nonneg C)
    intro a ha
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ha
    exact factor_sum_bounds hr hr2 hu hC hu0 (hmem d hd).1
      (hmem d hd).2.1 (hmem d hd).2.2
  rw [hcard] at hbound
  exact hbound

/-- The exact established variant recorded under Erdős problem 886. -/
theorem rosenfeld_bound :
    ∀ C > (0 : ℝ), ∀ᶠ (n : ℕ) in Filter.atTop,
    (((Nat.divisors n).filter (fun d : ℕ =>
      (n : ℝ) ^ (1/2 : ℝ) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ) + C * (n : ℝ) ^ (1/4 : ℝ))).card : ℝ)
      ≤ 1+C^2 := by
  intro C hC
  exact Filter.Eventually.of_forall (fun n => short_interval_bound n C hC.le)

end JSP000737
