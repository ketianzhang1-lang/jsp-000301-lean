import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# The quadratic obstruction in JSP-000388 / Erdos 477

An independently written formalization of a known obstruction. The original
existence question for arbitrary degree >= 2 has a positive answer; this file
does NOT prove that all polynomial value sets fail to tile the integers.
See README.md and PROVENANCE.md for scope and historical attribution.

Uniqueness concerns the pair of VALUES (an element of A and a polynomial value),
not the input of the polynomial. All sets and all integer parameters below are
unrestricted except for the explicitly stated leading-coefficient conditions.
-/

namespace JSP000388

/-- Every integer has a unique representation by an A-element and an f-value. -/
def ExactComplement (A : Set ℤ) (f : ℤ → ℤ) : Prop :=
  ∀ z : ℤ, ∃! p : ℤ × ℤ,
    p.1 ∈ A ∧ p.2 ∈ Set.range f ∧ p.1 + p.2 = z

def quadratic (a d c x : ℤ) : ℤ := a * (x ^ 2 + d * x) + c

/-- Every multiple of four is a difference of two values of x^2+d*x. -/
theorem normalized_difference (d t : ℤ) :
    ∃ x y : ℤ, (x ^ 2 + d * x) - (y ^ 2 + d * y) = 4 * t := by
  let e : ℤ := d / 2
  have hd : d = 2 * e ∨ d = 2 * e + 1 := by dsimp [e]; omega
  rcases hd with hd | hd
  · refine ⟨t + 1 - e, t - 1 - e, ?_⟩
    rw [hd]
    ring
  · refine ⟨2 * t - e, 2 * t - e - 1, ?_⟩
    rw [hd]
    ring

theorem quadratic_difference (a d c t : ℤ) :
    ∃ x y : ℤ, quadratic a d c x - quadratic a d c y = 4 * a * t := by
  obtain ⟨x, y, h⟩ := normalized_difference d t
  refine ⟨x, y, ?_⟩
  dsimp [quadratic]
  linear_combination a * h

/-- Equal sums force the same A-element; polynomial inputs need not be unique. -/
theorem left_unique {A : Set ℤ} {f : ℤ → ℤ} (h : ExactComplement A f)
    {u v x y : ℤ} (hu : u ∈ A) (hv : v ∈ A)
    (heq : u + f y = v + f x) : u = v := by
  obtain ⟨p, _, hp⟩ := h (u + f y)
  have h₁ : (u, f y) = p := hp (u, f y) ⟨hu, ⟨y, rfl⟩, rfl⟩
  have h₂ : (v, f x) = p := hp (v, f x) ⟨hv, ⟨x, rfl⟩, heq.symm⟩
  exact congrArg Prod.fst (h₁.trans h₂.symm)

/-- Any exact complement of this quadratic would be finite. -/
theorem complement_finite {a d c : ℤ} (ha : a ≠ 0) {A : Set ℤ}
    (h : ExactComplement A (quadratic a d c)) : A.Finite := by
  have hm : (4 : ℤ) * a ≠ 0 := mul_ne_zero (by norm_num) ha
  apply Set.Finite.of_injOn
    (f := fun u : ℤ => u % (4 * a))
    (t := Set.Ico 0 |4 * a|)
  · intro u _
    exact ⟨Int.emod_nonneg u hm, Int.emod_lt_abs u hm⟩
  · intro u hu v hv huv
    have hdvd : 4 * a ∣ u - v := by
      apply Int.dvd_iff_emod_eq_zero.mpr
      exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp huv
    obtain ⟨t, ht⟩ := hdvd
    obtain ⟨x, y, hxy⟩ := quadratic_difference a d c t
    apply left_unique h hu hv (x := x) (y := y)
    nlinarith
  · exact Set.finite_Ico 0 |4 * a|

theorem normalized_lower_bound (d x : ℤ) :
    -(d ^ 2) ≤ x ^ 2 + d * x := by
  nlinarith [sq_nonneg (2 * x + d), sq_nonneg d]

/-- The complete normalized quadratic family, with either sign of a. -/
theorem no_quadratic_complement (a d c : ℤ) (ha : a ≠ 0) (A : Set ℤ) :
    ¬ ExactComplement A (quadratic a d c) := by
  intro h
  have hf := complement_finite ha h
  rcases lt_or_gt_of_ne ha with ha | ha
  · obtain ⟨U, hU⟩ := hf.bddAbove
    obtain ⟨p, hp, _⟩ := h (U + c - a * d ^ 2 + 1)
    obtain ⟨x, hx⟩ := hp.2.1
    have hu := hU hp.1
    have hq := mul_le_mul_of_nonpos_left (normalized_lower_bound d x) (le_of_lt ha)
    have heq := hp.2.2
    dsimp [quadratic] at hx
    nlinarith
  · obtain ⟨L, hL⟩ := hf.bddBelow
    obtain ⟨p, hp, _⟩ := h (L + c - a * d ^ 2 - 1)
    obtain ⟨x, hx⟩ := hp.2.1
    have hl := hL hp.1
    have hq := mul_le_mul_of_nonneg_left (normalized_lower_bound d x) (le_of_lt ha)
    have heq := hp.2.2
    dsimp [quadratic] at hx
    nlinarith

/-- Covers every a*x^2+b*x+c with a != 0 and a dividing b, including b=0. -/
theorem no_divisible_quadratic_complement (a b c : ℤ) (ha : a ≠ 0)
    (hab : a ∣ b) (A : Set ℤ) :
    ¬ ExactComplement A (fun x => a * x ^ 2 + b * x + c) := by
  obtain ⟨d, rfl⟩ := hab
  have hf : (fun x : ℤ => a * x ^ 2 + a * d * x + c) = quadratic a d c := by
    funext x
    dsimp [quadratic]
    ring
  rw [hf]
  exact no_quadratic_complement a d c ha A

theorem no_square_complement (A : Set ℤ) :
    ¬ ExactComplement A (fun x : ℤ => x ^ 2) := by
  simpa using no_divisible_quadratic_complement 1 0 0 (by norm_num) (by simp) A

/-- The same statement with Mathlib polynomial evaluation and pair-value uniqueness. -/
theorem polynomial_quadratic_obstruction (a b c : ℤ) (ha : a ≠ 0)
    (hab : a ∣ b) (A : Set ℤ) :
    ∃ z : ℤ, ¬ ∃! p : ℤ × ℤ,
      p ∈ A ×ˢ Set.range (Polynomial.eval ·
        (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
          Polynomial.C c)) ∧ z = p.1 + p.2 := by
  by_contra h
  push Not at h
  apply no_divisible_quadratic_complement a b c ha hab A
  intro z
  obtain ⟨p, hp, huniq⟩ := h z
  refine ⟨p, ?_, ?_⟩
  · simpa only [Set.mem_prod, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, and_assoc, eq_comm] using hp
  · intro q hq
    apply huniq q
    simpa only [Set.mem_prod, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, and_assoc, eq_comm] using hq

end JSP000388
