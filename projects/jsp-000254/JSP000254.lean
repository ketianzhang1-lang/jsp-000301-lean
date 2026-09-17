/-
SPDX-License-Identifier: Apache-2.0
Definitions NoUnitFractionTriple and IsMaxNoTripleCard follow
Copyright 2025 The Formal Conjectures Authors (Apache-2.0).
New proof scripts: 2026 RECIPIENT-JSP-000254-KZ-A, with OpenAI Codex assistance.
-/
import Mathlib

/-!
JSP-000254 / Erdős 302: Cambie's five-eighths construction.
Mathematical construction: Stijn Cambie, as recorded in the Erdős problem archive
and google-deepmind/formal-conjectures, ErdosProblems/302.lean.
Formal proof development: RECIPIENT-JSP-000254-KZ-A with OpenAI Codex assistance, 2026.
This proves a known lower bound and refutes the proposed limit 1/2.
It does not determine the optimal asymptotic density.
-/

namespace JSP000254
open Finset Filter
open scoped Topology

def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

noncomputable def extremalCount (N : ℕ) : ℕ := by
  classical
  exact ((Icc 1 N).powerset.filter NoUnitFractionTriple).sup Finset.card

theorem extremalCount_isMax (N : ℕ) : IsMaxNoTripleCard N (extremalCount N) := by
  classical
  have hne : ((Icc 1 N).powerset.filter NoUnitFractionTriple).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩⟩
    simp [NoUnitFractionTriple]
  constructor
  · obtain ⟨A, hA, hcard⟩ := exists_mem_eq_sup _ hne Finset.card
    obtain ⟨hsub, hfree⟩ := mem_filter.mp hA
    exact ⟨A, mem_powerset.mp hsub, hfree, hcard.symm⟩
  · rintro k ⟨A, hsub, hfree, rfl⟩
    exact le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hsub, hfree⟩)

def cambieSet (t : ℕ) : Finset ℕ :=
  ((range t).image (fun i => 2 * i + 1)) ∪ Icc (4 * t + 1) (8 * t)

theorem mem_cambieSet {t a : ℕ} (ha : a ∈ cambieSet t) :
    0 < a ∧ a ≤ 8 * t ∧ ((a % 2 = 1 ∧ a < 2 * t) ∨ 4 * t < a) := by
  rcases mem_union.mp ha with h | h
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    simp only [mem_range] at hi
    omega
  · simp only [mem_Icc] at h
    omega

theorem cambieSet_subset (t : ℕ) : cambieSet t ⊆ Icc 1 (8 * t) := by
  intro a ha
  obtain ⟨h1, h2, _⟩ := mem_cambieSet ha
  exact mem_Icc.mpr ⟨h1, h2⟩

theorem cambieSet_card (t : ℕ) : (cambieSet t).card = 5 * t := by
  have hd : Disjoint ((range t).image (fun i => 2 * i + 1))
      (Icc (4 * t + 1) (8 * t)) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    simp only [mem_range] at hi
    simp only [mem_Icc] at hb
    omega
  rw [cambieSet, card_union_of_disjoint hd, card_image_of_injective _
    (by intro a b h; dsimp at h; omega), card_range, Nat.card_Icc]
  omega

private theorem equation_nat {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c) : a * b + a * c = b * c := by
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have hb' : (b : ℚ) ≠ 0 := by positivity
  have hc' : (c : ℚ) ≠ 0 := by positivity
  field_simp at h
  exact_mod_cast (by nlinarith : (a : ℚ) * b + a * c = b * c)

private theorem odd_obstruction {a b c : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (h : a * b + a * c = b * c) : False := by
  have hm := congrArg (fun n => n % 2) h
  rw [Nat.add_mod, Nat.mul_mod a b, Nat.mul_mod a c, Nat.mul_mod b c, ha, hb] at hm
  simp only [one_mul, Nat.mod_mod] at hm
  omega

theorem cambieSet_noTriple (t : ℕ) : NoUnitFractionTriple (cambieSet t) := by
  intro a ha b hb c hc _ _ _ heq
  obtain ⟨ha0, haN, ha⟩ := mem_cambieSet ha
  obtain ⟨hb0, hbN, hb⟩ := mem_cambieSet hb
  obtain ⟨hc0, hcN, hc⟩ := mem_cambieSet hc
  have he := equation_nat ha0 hb0 hc0 heq
  have hab : a < b := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right c h
    have h2 : 0 < a * b := Nat.mul_pos ha0 hb0
    omega
  have hac : a < c := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right b h
    have h2 : 0 < a * c := Nat.mul_pos ha0 hc0
    nlinarith
  rcases ha with ⟨haodd, haL⟩ | haH
  · rcases hb with ⟨hbodd, _⟩ | hbH
    · exact odd_obstruction haodd hbodd he
    rcases hc with ⟨hcodd, _⟩ | hcH
    · exact odd_obstruction (a := a) (b := c) (c := b) haodd hcodd (by nlinarith [he])
    have h1 := Nat.mul_lt_mul_of_pos_right (show 2 * a < b by omega) hc0
    have h2 := Nat.mul_lt_mul_of_pos_right (show 2 * a < c by omega) hb0
    nlinarith
  · have h1 := Nat.mul_lt_mul_of_pos_right (show b < 2 * a by omega) hc0
    have h2 := Nat.mul_lt_mul_of_pos_right (show c < 2 * a by omega) hb0
    nlinarith

theorem finite_lower_bound (N : ℕ) :
    ∃ A ⊆ Icc 1 N, NoUnitFractionTriple A ∧ A.card = 5 * (N / 8) := by
  refine ⟨cambieSet (N / 8), ?_, cambieSet_noTriple _, cambieSet_card _⟩
  intro a ha
  obtain ⟨ha1, ha2⟩ := mem_Icc.mp (cambieSet_subset _ ha)
  exact mem_Icc.mpr ⟨ha1, ha2.trans (Nat.mul_div_le N 8)⟩

theorem max_card_lower_bound (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (N : ℕ) : 5 * (N / 8) ≤ f N := by
  obtain ⟨A, hA, hfree, hcard⟩ := finite_lower_bound N
  exact (hf N).2 ⟨A, hA, hfree, hcard⟩

theorem real_lower_bound (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (N : ℕ) : (5 : ℝ) / 8 * N - 5 ≤ f N := by
  have h := max_card_lower_bound f hf N
  have hdiv : N ≤ 8 * (N / 8) + 7 := by omega
  have hc : (N : ℝ) ≤ 8 * (N / 8 : ℕ) + 7 := by exact_mod_cast hdiv
  have hf' : (5 : ℝ) * (N / 8 : ℕ) ≤ f N := by exact_mod_cast h
  linarith

theorem lower_five_eighths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((5 : ℝ) / ε)
  filter_upwards [eventually_ge_atTop M] with N hN
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : (5 : ℝ) ≤ ε * N := by
    have := (div_lt_iff₀ hε).mp hM
    nlinarith
  have h := real_lower_bound f hf N
  nlinarith

theorem not_tendsto_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) := by
  intro h
  have hu : ∀ᶠ N : ℕ in atTop, (f N : ℝ) / N < 9 / 16 :=
    (tendsto_order.mp h).2 (9 / 16) (by norm_num)
  have hl := lower_five_eighths f hf (1 / 16) (by norm_num)
  obtain ⟨N, hN, huN, hlN⟩ := (eventually_ge_atTop 1 |>.and (hu.and hl)).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht := (div_lt_iff₀ hNpos).mp huN
  norm_num at hlN
  linarith

theorem extremal_not_tendsto_half :
    ¬ Tendsto (fun N : ℕ => (extremalCount N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) :=
  not_tendsto_half extremalCount extremalCount_isMax

end JSP000254

/- The following definitions and theorem statements match the selected upstream
   statements at formal-conjectures commit 40e7c98697de6f66b8cbdbf641749ab39ed9c152.
   No upstream file containing admitted proofs is imported. -/
namespace Erdos302
open Filter Finset
open scoped Topology

def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

theorem erdos_302.variants.lower_five_eighths (f : ℕ → ℕ)
    (hf : ∀ N, IsMaxNoTripleCard N (f N)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N :=
  JSP000254.lower_five_eighths f hf ε hε

theorem erdos_302.parts.ii (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) :=
  JSP000254.not_tendsto_half f hf

end Erdos302
