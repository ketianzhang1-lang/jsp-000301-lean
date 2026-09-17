/-
Copyright 2026. Licensed under the Apache License, Version 2.0.

JSP-000554 / Erdős 682: the unconditional finite-residue reduction from
Gafni and Tao, Rough numbers between consecutive primes, Section 4.
This does not prove the asymptotic estimate in their Theorem 1.1.
Independently written with OpenAI ChatGPT assistance.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

namespace JSP000554
open Finset

/-- Product of the primes strictly below the gap length. -/
def primorial (h : ℕ) : ℕ := ∏ q ∈ (range h).filter Nat.Prime, q

/-- A prime gap of length h with no interior number whose least prime factor is >= h. -/
def BadGap (p h : ℕ) : Prop :=
  p.Prime ∧ (p + h).Prime ∧
  (∀ m, p < m → m < p + h → ¬ m.Prime) ∧
  ∀ m, p < m → m < p + h → m.minFac < h

/-- The finite residue classes in the exact reduction in Section 4. -/
def omegaSet (h : ℕ) : Finset ℕ :=
  (range (primorial h)).filter fun b =>
    b.Coprime (primorial h) ∧ (b + h).Coprime (primorial h) ∧
    ∀ j ∈ Ioo 0 h, ¬ (b + j).Coprime (primorial h)

theorem primorial_pos (h : ℕ) : 0 < primorial h := by
  apply Finset.prod_pos
  intro q hq
  exact (Finset.mem_filter.mp hq).2.pos

theorem coprime_primorial_iff (n h : ℕ) :
    n.Coprime (primorial h) ↔ ∀ q, q < h → q.Prime → ¬ q ∣ n := by
  simp only [primorial, Nat.coprime_prod_right_iff, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · intro hn q hq hprime hd
    exact ((hprime.coprime_iff_not_dvd).mp ((hn q ⟨hq, hprime⟩).symm)) hd
  · intro hn q hq
    exact ((hq.2.coprime_iff_not_dvd).mpr (hn q hq.1 hq.2)).symm

theorem minFac_lt_iff_not_coprime {n h : ℕ} (hn : 1 < n) :
    n.minFac < h ↔ ¬ n.Coprime (primorial h) := by
  rw [coprime_primorial_iff]
  constructor
  · intro hsmall hall
    exact hall n.minFac hsmall (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
  · intro hnot
    push Not at hnot
    obtain ⟨q, hq, hprime, hd⟩ := hnot
    exact lt_of_le_of_lt (Nat.minFac_le_of_dvd hprime.two_le hd) hq

theorem prime_coprime_primorial {p h : ℕ} (hp : p.Prime) (hh : h ≤ p) :
    p.Coprime (primorial h) := by
  rw [coprime_primorial_iff]
  intro q hq hprime hd
  have := (Nat.dvd_prime hp).mp hd
  rcases this with heq | heq
  · exact hprime.ne_one heq
  · omega

theorem coprime_mod_add (p M j : ℕ) :
    (p % M + j).Coprime M ↔ (p + j).Coprime M := by
  change Nat.gcd (p % M + j) M = 1 ↔ Nat.gcd (p + j) M = 1
  have hmod (a : ℕ) : Nat.gcd (a % M) M = Nat.gcd a M := by
    rw [← Nat.gcd_rec M a, Nat.gcd_comm]
  rw [← hmod (p % M + j), ← hmod (p + j)]
  rw [Nat.mod_add_mod]

/-- The paper's residue reduction, valid for every length and every large-enough prime pair.
The right side does not assume that the primes are consecutive: this is proved. -/
theorem badGap_iff_residue {p h : ℕ} (hh : 2 ≤ h) (hp : h ≤ p) :
    BadGap p h ↔ p.Prime ∧ (p + h).Prime ∧ p % primorial h ∈ omegaSet h := by
  constructor
  · rintro ⟨hprime, hprime', _, hrough⟩
    refine ⟨hprime, hprime', ?_⟩
    rw [omegaSet, mem_filter]
    refine ⟨mem_range.mpr (Nat.mod_lt _ (primorial_pos h)), ?_, ?_, ?_⟩
    · simpa using (coprime_mod_add p (primorial h) 0).mpr
        (prime_coprime_primorial hprime hp)
    · exact (coprime_mod_add p (primorial h) h).mpr
        (prime_coprime_primorial hprime' (by omega))
    · intro j hj
      have hj' := mem_Ioo.mp hj
      rw [coprime_mod_add]
      exact (minFac_lt_iff_not_coprime (by omega)).mp (hrough (p + j) (by omega) (by omega))
  · rintro ⟨hprime, hprime', hmem⟩
    have hres := (mem_filter.mp hmem).2.2.2
    have hrough : ∀ m, p < m → m < p + h → m.minFac < h := by
      intro m hm hm'
      have := hres (m - p) (mem_Ioo.mpr (by omega))
      rw [coprime_mod_add, Nat.add_sub_of_le (by omega : p ≤ m)] at this
      exact (minFac_lt_iff_not_coprime (by omega)).mpr this
    refine ⟨hprime, hprime', ?_, hrough⟩
    intro m hm hm' hmp
    have := hrough m hm hm'
    rw [hmp.minFac_eq] at this
    omega

/-- Bertrand's postulate rules out exceptional gaps starting below their length. -/
theorem badGap_start_ge_length {p h : ℕ} (hb : BadGap p h) : h ≤ p := by
  by_contra hn
  obtain ⟨q, hqp, hpq, hq⟩ := Nat.exists_prime_lt_and_le_two_mul p (by
    have := hb.1.two_le
    omega)
  exact hb.2.2.1 q hpq (by omega) hqp

/-- Version without a restriction on the starting point. -/
theorem badGap_iff_residue_all {p h : ℕ} (hh : 2 ≤ h) :
    BadGap p h ↔ h ≤ p ∧ p.Prime ∧ (p + h).Prime ∧ p % primorial h ∈ omegaSet h := by
  constructor
  · intro hb
    exact ⟨badGap_start_ge_length hb,
      (badGap_iff_residue hh (badGap_start_ge_length hb)).mp hb⟩
  · rintro ⟨hp, hb⟩
    exact (badGap_iff_residue hh hp).mpr hb

section Counting
attribute [local instance] Classical.propDecidable

/-- Exact finite counting formula, with no prime-tuples conjecture or asymptotic assumptions. -/
theorem count_badGaps (s : Finset ℕ) (h : ℕ) (hh : 2 ≤ h)
    (hs : ∀ p ∈ s, h ≤ p) :
    (s.filter fun p => BadGap p h).card =
      ∑ b ∈ omegaSet h,
        (s.filter fun p => p.Prime ∧ (p + h).Prime ∧ p % primorial h = b).card := by
  classical
  let t := s.filter fun p => p.Prime ∧ (p + h).Prime
  have heq : (s.filter fun p => BadGap p h) =
      t.filter (fun p => p % primorial h ∈ omegaSet h) := by
    ext p
    simp only [mem_filter, t]
    constructor
    · rintro ⟨hps, hb⟩
      obtain ⟨hpr, hpr', hr⟩ := (badGap_iff_residue hh (hs p hps)).mp hb
      exact ⟨⟨hps, hpr, hpr'⟩, hr⟩
    · rintro ⟨⟨hps, hpr, hpr'⟩, hr⟩
      exact ⟨hps, (badGap_iff_residue hh (hs p hps)).mpr ⟨hpr, hpr', hr⟩⟩
  rw [heq, ← Finset.sum_card_fiberwise_eq_card_filter t (omegaSet h)]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ext p
  simp only [mem_filter, t]
  tauto

/-- The same exact formula for an arbitrary finite set of starting points. -/
theorem count_badGaps_all (s : Finset ℕ) (h : ℕ) (hh : 2 ≤ h) :
    (s.filter fun p => BadGap p h).card =
      ∑ b ∈ omegaSet h,
        (s.filter fun p => h ≤ p ∧ p.Prime ∧ (p + h).Prime ∧ p % primorial h = b).card := by
  have heq : (s.filter fun p => BadGap p h) =
      (s.filter fun p => h ≤ p).filter (fun p => BadGap p h) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hps, hb⟩
      exact ⟨⟨hps, badGap_start_ge_length hb⟩, hb⟩
    · tauto
  rw [heq, count_badGaps _ h hh (by intro p hp; exact (mem_filter.mp hp).2)]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ext p
  simp only [mem_filter]
  tauto

end Counting

set_option maxRecDepth 100000 in
theorem primorial_values :
    primorial 2 = 1 ∧ primorial 4 = 6 ∧ primorial 6 = 30 ∧
    primorial 8 = 210 ∧ primorial 10 = 210 ∧ primorial 12 = 2310 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem omega_two : omegaSet 2 = ∅ := by decide +kernel

set_option maxRecDepth 100000 in
theorem omega_four : omegaSet 4 = {1} := by decide +kernel

set_option maxRecDepth 100000 in
theorem omega_six : omegaSet 6 = {1, 23} := by decide +kernel

set_option maxRecDepth 100000 in
theorem omega_eight : omegaSet 8 = {89, 113} := by decide +kernel

set_option maxRecDepth 100000 in
theorem omega_ten : omegaSet 10 = {1, 199} := by decide +kernel

set_option maxRecDepth 100000 in
theorem omega_twelve : omegaSet 12 = {1, 199, 467, 509, 1789, 1831, 2099, 2297} := by
  decide +kernel

theorem no_bad_twin_gap (p : ℕ) : ¬ BadGap p 2 := by
  rw [badGap_iff_residue_all (by omega), omega_two]
  simp

theorem gap_four_classification (p : ℕ) :
    BadGap p 4 ↔ 4 ≤ p ∧ p.Prime ∧ (p + 4).Prime ∧ p % 6 = 1 := by
  rw [badGap_iff_residue_all (by omega), omega_four, primorial_values.2.1]
  simp

theorem gap_six_classification (p : ℕ) :
    BadGap p 6 ↔ 6 ≤ p ∧ p.Prime ∧ (p + 6).Prime ∧ p % 30 ∈ ({1, 23} : Finset ℕ) := by
  rw [badGap_iff_residue_all (by omega), omega_six, primorial_values.2.2.1]

theorem gap_eight_classification (p : ℕ) :
    BadGap p 8 ↔ 8 ≤ p ∧ p.Prime ∧ (p + 8).Prime ∧ p % 210 ∈ ({89, 113} : Finset ℕ) := by
  rw [badGap_iff_residue_all (by omega), omega_eight, primorial_values.2.2.2.1]

theorem gap_ten_classification (p : ℕ) :
    BadGap p 10 ↔ 10 ≤ p ∧ p.Prime ∧ (p + 10).Prime ∧ p % 210 ∈ ({1, 199} : Finset ℕ) := by
  rw [badGap_iff_residue_all (by omega), omega_ten, primorial_values.2.2.2.2.1]

theorem gap_twelve_classification (p : ℕ) :
    BadGap p 12 ↔ 12 ≤ p ∧ p.Prime ∧ (p + 12).Prime ∧
      p % 2310 ∈ ({1, 199, 467, 509, 1789, 1831, 2099, 2297} : Finset ℕ) := by
  rw [badGap_iff_residue_all (by omega), omega_twelve, primorial_values.2.2.2.2.2]

end JSP000554
