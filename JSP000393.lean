/-
Copyright (c) 2026 Ketian Zhang. Released under the MIT license.
AI-assisted Lean formalization prepared with OpenAI Codex.
Mathematical seed: Coppersmith and Davenport, Acta Arith. 58 (1991), p. 86.
The sparse product amplification is classical; no new mathematical discovery
or first-formalization priority is claimed.
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
A Coppersmith--Davenport sparse-square seed and its separated-digit products.
This formalizes a constructive component related to JSP-000393 / Erdos 485,
not Schinzel's theorem that the minimum square support tends to infinity.
-/
namespace JSP000393
open Polynomial Finset

noncomputable def seed : ℤ[X] :=
  (125 * X^6 + 50 * X^5 - 10 * X^4 + 4 * X^3 - 2 * X^2 + 2 * X + 1) *
    (1 - 110 * X^6)

lemma support_sparse_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (e : α → ℕ) (c : α → ℤ)
    (he : Set.InjOn e s) (hc : ∀ i ∈ s, c i ≠ 0) :
    (∑ i ∈ s, monomial (e i) (c i)).support = s.image e := by
  classical
  ext n
  simp only [mem_support_iff, finsetSum_coeff, coeff_monomial, mem_image]
  constructor
  · intro h
    obtain ⟨i, hi, hn⟩ := exists_ne_zero_of_sum_ne_zero h
    refine ⟨i, hi, ?_⟩
    split_ifs at hn with hni
    · exact hni
    · exact False.elim (hn rfl)
  · rintro ⟨i, hi, rfl⟩
    rw [sum_eq_single_of_mem i hi, ite_eq_left rfl]
    · exact hc i hi
    · intro j hj hji
      exact ite_eq_right (fun h => hji (he hj hi h))

lemma card_support_mul_expand (p q : ℤ[X]) (b : ℕ) (hp : p.natDegree < b) :
    (p * expand ℤ b q).support.card = p.support.card * q.support.card := by
  classical
  let s := p.support ×ˢ q.support
  let e := fun ij : ℕ × ℕ => ij.1 + ij.2 * b
  let c := fun ij : ℕ × ℕ => p.coeff ij.1 * q.coeff ij.2
  have he : Set.InjOn e s := by
    intro x hx y hy hxy
    have hx' : x.1 < b := lt_of_le_of_lt (le_natDegree_of_mem_supp _
      (mem_product.mp hx).1) hp
    have hy' : y.1 < b := lt_of_le_of_lt (le_natDegree_of_mem_supp _
      (mem_product.mp hy).1) hp
    have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hp
    dsimp [e] at hxy
    have hfirst : x.1 = y.1 := by
      have hmod := congrArg (fun n => n % b) hxy
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] using hmod
    have hsecond : x.2 = y.2 := by nlinarith
    exact Prod.ext hfirst hsecond
  have hc : ∀ i ∈ s, c i ≠ 0 := by
    intro i hi
    exact mul_ne_zero (mem_support_iff.mp (mem_product.mp hi).1)
      (mem_support_iff.mp (mem_product.mp hi).2)
  have hrepr : p * expand ℤ b q = ∑ i ∈ s, monomial (e i) (c i) := by
    conv_lhs => rw [p.as_sum_support, q.as_sum_support]
    simp only [map_sum, expand_monomial, sum_mul, mul_sum, monomial_mul_monomial]
    rw [sum_product]
    exact sum_comm
  rw [hrepr, support_sparse_sum s e c he hc, card_image_of_injOn he, card_product]


def seedExponents : Fin 13 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def seedCoefficients : Fin 13 → ℤ := ![1, 2, -2, 4, -10, 50, 15, -220, 220, -440, 1100, -5500, -13750]

lemma seed_expansion : seed =
    ∑ i : Fin 13, monomial (seedExponents i) (seedCoefficients i) := by
  norm_num [seed, seedExponents, seedCoefficients, Fin.sum_univ_succ,
    ← C_mul_X_pow_eq_monomial]
  ring

lemma seed_support_card : (seed).support.card = 13 := by
  rw [seed_expansion, support_sparse_sum]
  · rw [card_image_of_injective _ (by decide : Function.Injective seedExponents)]
    exact card_fin 13
  · exact (by decide : Function.Injective seedExponents).injOn
  · intro i _
    fin_cases i <;> norm_num [seedCoefficients]

lemma seed_degree_bound : (seed).natDegree < 25 := by
  rw [seed_expansion]
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_) (by decide : 24 < 25)
  intro i _
  apply le_trans (natDegree_monomial_le _) ?_
  fin_cases i <;> norm_num [seedExponents]

def squareExponents : Fin 12 → ℕ := ![0, 1, 5, 6, 7, 11, 12, 17, 18, 19, 23, 24]
def squareCoefficients : Fin 12 → ℤ := ![1, 4, 44, 286, -660, 2820, -83595, -2217600, 2685100, 2662000, 151250000, 189062500]

lemma square_expansion : seed ^ 2 =
    ∑ i : Fin 12, monomial (squareExponents i) (squareCoefficients i) := by
  norm_num [seed, squareExponents, squareCoefficients, Fin.sum_univ_succ,
    ← C_mul_X_pow_eq_monomial]
  ring

lemma square_support_card : (seed ^ 2).support.card = 12 := by
  rw [square_expansion, support_sparse_sum]
  · rw [card_image_of_injective _ (by decide : Function.Injective squareExponents)]
    exact card_fin 12
  · exact (by decide : Function.Injective squareExponents).injOn
  · intro i _
    fin_cases i <;> norm_num [squareCoefficients]

lemma square_degree_bound : (seed ^ 2).natDegree < 25 := by
  rw [square_expansion]
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_) (by decide : 24 < 25)
  intro i _
  apply le_trans (natDegree_monomial_le _) ?_
  fin_cases i <;> norm_num [squareExponents]


/-- Separated base-25 blocks; squaring the seed has degree at most 24. -/
noncomputable def family : ℕ → ℤ[X]
  | 0 => 1
  | k + 1 => seed * expand ℤ 25 (family k)

/-- Exact support counts, including the constant polynomial at k = 0. -/
theorem family_counts (k : ℕ) :
    (family k).support.card = 13 ^ k ∧ ((family k)^2).support.card = 12 ^ k := by
  induction k with
  | zero =>
    have h : (1 : ℤ[X]).support = {0} := by
      simpa only [map_one] using (support_C (a := (1 : ℤ)) (by decide))
    simp [family, h]
  | succ k ih =>
    constructor
    · rw [family, card_support_mul_expand _ _ _ seed_degree_bound, seed_support_card,
        ih.1, pow_succ, mul_comm]
    · rw [family, mul_pow, ← map_pow, card_support_mul_expand _ _ _ square_degree_bound,
        square_support_card, ih.2, pow_succ, mul_comm]

lemma growth (k : ℕ) : (k + 12) * 12 ^ k ≤ 12 * 13 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    simp only [pow_succ]
    nlinarith [Nat.zero_le (k * 12 ^ k)]

/-- The ratio between the original and squared support is unbounded.
This is a known constructive component, not the full Schinzel lower-bound theorem. -/
theorem arbitrarily_sparse_squares (M : ℕ) :
    ∃ p : ℤ[X], M * (p ^ 2).support.card < p.support.card := by
  refine ⟨family (12 * M), ?_⟩
  rw [(family_counts _).1, (family_counts _).2]
  have hg := growth (12 * M)
  have hp : 0 < 12 ^ (12 * M) := pow_pos (by decide) _
  nlinarith

#print axioms family_counts
#print axioms arbitrarily_sparse_squares
end JSP000393
