import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# JSP-000264 / Erdős 318, positive-density counterexample

An independently written formalization of the known counterexample consisting
of all odd positive integers and 2. Mathematical attribution belongs to Erdős
(as credited by Sattler, 1982). This proves part (i), not the full collection of
questions, in particular not the squares-without-1 theorem.

The P₁ definition follows Formal Conjectures (Apache-2.0, see PROVENANCE.md).
-/

namespace JSP000264
open Filter
open scoped Topology

/-- Nonconstant signs on the nonzero elements admit a nonempty zero-sum subset. -/
def P₁ (A : Set ℕ) : Prop := ∀ (f : ℕ → ℝ),
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) →
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => -1) →
  Set.range f ⊆ {1, -1} →
  ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ A \ {0} ∧ ∑ n ∈ S, f n / n = 0

/-- Standard natural density: the number of elements below N, divided by N. -/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) / N) atTop (𝓝 d)

def counterexampleSet : Set ℕ := {n | Odd n ∨ n = 2}

/-- A finite sum of reciprocals of odd natural numbers has an odd denominator. -/
theorem odd_denominator (S : Finset ℕ) (hS : ∀ n ∈ S, Odd n) :
    ∃ p q : ℕ, Odd q ∧ 0 < q ∧ ∑ n ∈ S, (1 : ℝ) / n = p / q := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 1, by decide, by decide, by simp⟩
  | @insert a S ha ih =>
    have hao : Odd a := hS a (by simp)
    obtain ⟨p, q, hqo, hq, heq⟩ := ih (fun n hn => hS n (by simp [hn]))
    refine ⟨q + a * p, a * q, hao.mul hqo, Nat.mul_pos hao.pos hq, ?_⟩
    rw [Finset.sum_insert ha, heq]
    push_cast
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast hao.pos.ne'
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp <;> ring

/-- All odds together with 2 fail P₁, even though the chosen signs are nonconstant. -/
theorem counterexample_not_P₁ : ¬ P₁ counterexampleSet := by
  classical
  intro hP
  let f : ℕ → ℝ := fun n => if n = 2 then 1 else -1
  have h1 : 1 ∈ counterexampleSet \ {0} := by norm_num [counterexampleSet]
  have h2 : 2 ∈ counterexampleSet \ {0} := by simp [counterexampleSet]
  have hf1 : f ∘ (Subtype.val : (counterexampleSet \ {0} : Set ℕ) → ℕ) ≠
      (fun _ => 1) := by
    intro h
    have := congr_fun h ⟨1, h1⟩
    norm_num [f, Function.comp_def] at this
  have hf2 : f ∘ (Subtype.val : (counterexampleSet \ {0} : Set ℕ) → ℕ) ≠
      (fun _ => -1) := by
    intro h
    have := congr_fun h ⟨2, h2⟩
    norm_num [f, Function.comp_def] at this
  have hfr : Set.range f ⊆ {1, -1} := by
    rintro x ⟨n, rfl⟩
    by_cases hn : n = 2 <;> simp [f, hn]
  obtain ⟨S, hne, hsub, hz⟩ := hP f hf1 hf2 hfr
  by_cases h2S : 2 ∈ S
  · have ho : ∀ n ∈ S.erase 2, Odd n := by
      intro n hn
      have hmem := Finset.mem_erase.mp hn
      exact (hsub hmem.2).1.resolve_right hmem.1
    obtain ⟨p, q, hqo, hq, hsum⟩ := odd_denominator (S.erase 2) ho
    have hneg : ∑ n ∈ S.erase 2, f n / n = -(∑ n ∈ S.erase 2, (1 : ℝ) / n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      simp [f, (Finset.mem_erase.mp hn).1]
    have heq := Finset.add_sum_erase S (fun n => f n / n) h2S
    rw [hz, hneg, hsum] at heq
    have hrat : (1 : ℝ) / 2 = (p : ℝ) / q := by
      norm_num [f] at heq
      linarith
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have heqR : (q : ℝ) = 2 * p := by
      field_simp at hrat
      linarith
    have heqN : q = 2 * p := by exact_mod_cast heqR
    exact hqo.not_two_dvd_nat ⟨p, heqN⟩
  · have hlt : ∑ n ∈ S, f n / n < 0 := by
      apply Finset.sum_neg _ hne
      intro n hn
      have hn2 : n ≠ 2 := by intro h; subst n; exact h2S hn
      have hn0 : n ≠ 0 := by simpa using (hsub hn).2
      have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      simpa [f, hn2] using div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hnr
    linarith

theorem odd_count (N : ℕ) : ((Finset.range N).filter Odd).card = N / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases ho : Odd N
    · simp [ho, ih]
      have := Nat.odd_iff.mp ho
      omega
    · simp [ho, ih]
      have := Nat.not_odd_iff.mp ho
      omega

/-- Exact counting formula, not merely a positive lower-density bound. -/
theorem counterexample_count (N : ℕ) (hN : 3 ≤ N) :
    (counterexampleSet ∩ Set.Iio N).ncard = N / 2 + 1 := by
  classical
  have heq : counterexampleSet ∩ Set.Iio N =
      (↑(insert 2 ((Finset.range N).filter Odd)) : Set ℕ) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Iio, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_filter, Finset.mem_range, counterexampleSet, Set.mem_setOf_eq]
    omega
  rw [heq, Set.ncard_coe_finset, Finset.card_insert_of_notMem]
  · rw [odd_count]
  · simp

/-- The counterexample has natural density exactly 1/2. -/
theorem counterexample_density : HasNaturalDensity counterexampleSet (1 / 2) := by
  have hup : Tendsto (fun N : ℕ => (1 : ℝ) / 2 + 1 / N) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_ge_atTop 3] with N hN
    rw [counterexample_count N hN]
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    apply (le_div_iff₀ hn).2
    have hnat : N ≤ 2 * (N / 2 + 1) := by omega
    have hr : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) + 1 : ℝ) := by exact_mod_cast hnat
    push_cast
    linarith
  · filter_upwards [eventually_ge_atTop 3] with N hN
    rw [counterexample_count N hN]
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    apply (div_le_iff₀ hn).2
    have hnat : 2 * (N / 2) ≤ N := by omega
    have hr : 2 * (N / 2 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hnat
    push_cast
    field_simp
    nlinarith

/-- Complete positive-density existence part of Erdős 318. -/
theorem positive_density_counterexample :
    ∃ A : Set ℕ, (∃ d : ℝ, 0 < d ∧ HasNaturalDensity A d) ∧ ¬ P₁ A := by
  exact ⟨counterexampleSet, ⟨1 / 2, by norm_num, counterexample_density⟩,
    counterexample_not_P₁⟩

end JSP000264
