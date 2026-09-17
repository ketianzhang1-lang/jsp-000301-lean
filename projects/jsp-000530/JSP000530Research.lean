import JSP000530
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Research toward the unresolved parts of JSP-000530 / Erdős 654

We contribute these reductions and obstruction lemmas under GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT assistance. This file does not assert a
complete solution. In particular, `UniformDistanceImprovement` is a definition
of a remaining target, not an axiom or a theorem claiming it has been proved.
-/

namespace JSP000530.Research
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Coordinate determinant: zero exactly when the three planar points are collinear. -/
def areaDet (a b c : ℂ) : ℝ :=
  (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)

def NoThreeCollinear (S : Finset ℂ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
    a ≠ b → a ≠ c → b ≠ c → areaDet a b c ≠ 0

def distanceFiber (S : Finset ℂ) (p : ℂ) (r : ℝ) : Finset ℂ := by
  classical
  exact (S.erase p).filter (fun q => dist p q = r)

def fiberSlack (S : Finset ℂ) (p : ℂ) : ℕ :=
  ∑ r ∈ distanceValues S p, (3 - (distanceFiber S p r).card)

def multiplicityCount (S : Finset ℂ) (p : ℂ) (k : ℕ) : ℕ :=
  ((distanceValues S p).filter (fun r => (distanceFiber S p r).card = k)).card

theorem distance_fiber_le_three {S : Finset ℂ} (hS : NoFourConcyclic S)
    (p : ℂ) (r : ℝ) : (distanceFiber S p r).card ≤ 3 := by
  classical
  refine (card_le_card ?_).trans (hS p r)
  intro q hq
  obtain ⟨hmem, hd⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨(mem_erase.mp hmem).2, by simpa [dist_comm] using hd⟩

theorem sum_distance_fibers (S : Finset ℂ) (p : ℂ) :
    ∑ r ∈ distanceValues S p, (distanceFiber S p r).card = (S.erase p).card := by
  classical
  exact (card_eq_sum_card_image (dist p) (S.erase p)).symm

/-- Slack counts singleton distance classes twice and doubleton classes once. -/
theorem slack_eq_small_fibers {S : Finset ℂ} (hS : NoFourConcyclic S) (p : ℂ) :
    fiberSlack S p = 2 * multiplicityCount S p 1 + multiplicityCount S p 2 := by
  classical
  calc
    fiberSlack S p =
        (∑ r ∈ distanceValues S p, if (distanceFiber S p r).card = 1 then 2 else 0) +
        ∑ r ∈ distanceValues S p, if (distanceFiber S p r).card = 2 then 1 else 0 := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro r hr
      have hu := distance_fiber_le_three hS p r
      obtain ⟨q, hq, hqr⟩ := mem_image.mp hr
      have hl : 1 ≤ (distanceFiber S p r).card := card_pos.mpr
        ⟨q, mem_filter.mpr ⟨hq, hqr⟩⟩
      by_cases h1 : (distanceFiber S p r).card = 1
      · simp [h1]
      by_cases h2 : (distanceFiber S p r).card = 2
      · simp [h2]
      have h3 : (distanceFiber S p r).card = 3 := by omega
      simp [h3]
    _ = 2 * multiplicityCount S p 1 + multiplicityCount S p 2 := by
      simp only [← sum_filter]
      simp [multiplicityCount, Nat.mul_comm]

/-- Exact accounting identity, including the excluded base point. -/
theorem slack_identity {S : Finset ℂ} (hS : NoFourConcyclic S) {p : ℂ}
    (hp : p ∈ S) : S.card - 1 + fiberSlack S p = 3 * (distanceValues S p).card := by
  classical
  have h := sum_distance_fibers S p
  rw [card_erase_of_mem hp] at h
  calc
    S.card - 1 + fiberSlack S p =
        (∑ r ∈ distanceValues S p, (distanceFiber S p r).card) +
          ∑ r ∈ distanceValues S p, (3 - (distanceFiber S p r).card) := by rw [h]; rfl
    _ = ∑ r ∈ distanceValues S p,
        ((distanceFiber S p r).card + (3 - (distanceFiber S p r).card)) := by
      rw [sum_add_distrib]
    _ = ∑ _ ∈ distanceValues S p, 3 := by
      apply sum_congr rfl
      intro r _
      exact Nat.add_sub_of_le (distance_fiber_le_three hS p r)
    _ = 3 * (distanceValues S p).card := by simp [Nat.mul_comm]

/-- The classical one-third baseline; this is not a positive constant improvement. -/
theorem one_third_bound {S : Finset ℂ} (hS : NoFourConcyclic S) {p : ℂ}
    (hp : p ∈ S) : S.card - 1 ≤ 3 * (distanceValues S p).card := by
  have h := slack_identity hS hp
  omega

theorem slack_identity_real {S : Finset ℂ} (hS : NoFourConcyclic S) {p : ℂ}
    (hp : p ∈ S) : (S.card : ℝ) - 1 + (fiberSlack S p : ℝ) =
      3 * ((distanceValues S p).card : ℝ) := by
  have hn : 1 ≤ S.card := card_pos.mpr ⟨p, hp⟩
  have h := congrArg (fun n : ℕ => (n : ℝ)) (slack_identity hS hp)
  simpa only [Nat.cast_add, Nat.cast_sub hn, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] using h

/-- The geometric improvement needed is linear slack, not merely nonzero slack. -/
theorem improvement_iff_linear_slack {S : Finset ℂ} (hS : NoFourConcyclic S)
    {p : ℂ} (hp : p ∈ S) (c : ℝ) :
    (1 / 3 + c) * (S.card : ℝ) < ((distanceValues S p).card : ℝ) ↔
      3 * c * (S.card : ℝ) + 1 < (fiberSlack S p : ℝ) := by
  have h := slack_identity_real hS hp
  constructor <;> intro hlt <;> nlinarith

/-- A remaining original target. No proof of this proposition is asserted. -/
def UniformDistanceImprovement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ S : Finset ℂ,
    N ≤ S.card → NoFourConcyclic S →
      ∃ p ∈ S, (1 / 3 + c) * (S.card : ℝ) < ((distanceValues S p).card : ℝ)

/-- The corresponding remaining target with the extra general-position condition. -/
def GeneralPositionImprovement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ S : Finset ℂ,
    N ≤ S.card → NoFourConcyclic S → NoThreeCollinear S →
      ∃ p ∈ S, (1 / 3 + c) * (S.card : ℝ) < ((distanceValues S p).card : ℝ)

def UniformSlackImprovement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ S : Finset ℂ,
    N ≤ S.card → NoFourConcyclic S →
      ∃ p ∈ S, δ * (S.card : ℝ) + 1 < (fiberSlack S p : ℝ)

/-- Exact reformulation of the unresolved uniform lower-bound target. -/
theorem uniform_improvement_iff_slack :
    UniformDistanceImprovement ↔ UniformSlackImprovement := by
  constructor
  · rintro ⟨c, hc, N, h⟩
    refine ⟨3*c, mul_pos (by norm_num) hc, N, ?_⟩
    intro S hN hS
    obtain ⟨p, hp, hd⟩ := h S hN hS
    exact ⟨p, hp, (improvement_iff_linear_slack hS hp c).mp hd⟩
  · rintro ⟨δ, hδ, N, h⟩
    refine ⟨δ/3, div_pos hδ (by norm_num), N, ?_⟩
    intro S hN hS
    obtain ⟨p, hp, hd⟩ := h S hN hS
    refine ⟨p, hp, (improvement_iff_linear_slack hS hp (δ/3)).mpr ?_⟩
    nlinarith

/-- Three centers equidistant from one fixed distinct pair must be collinear. -/
theorem equidistant_centers_collinear {a b c u v : ℂ} (huv : u ≠ v)
    (ha : sqDist a u = sqDist a v) (hb : sqDist b u = sqDist b v)
    (hc : sqDist c u = sqDist c v) : areaDet a b c = 0 := by
  have hB : (b.re-a.re)*(u.re-v.re) + (b.im-a.im)*(u.im-v.im) = 0 := by
    dsimp [sqDist] at ha hb
    nlinarith
  have hC : (c.re-a.re)*(u.re-v.re) + (c.im-a.im)*(u.im-v.im) = 0 := by
    dsimp [sqDist] at ha hc
    nlinarith
  by_cases hx : u.re = v.re
  · have hy : u.im ≠ v.im := fun h => huv (Complex.ext hx h)
    have hprod : (u.im-v.im) * areaDet a b c = 0 := by
      calc
        _ = ((c.re-a.re)*(u.re-v.re) + (c.im-a.im)*(u.im-v.im))*(b.re-a.re) -
          ((b.re-a.re)*(u.re-v.re) + (b.im-a.im)*(u.im-v.im))*(c.re-a.re) := by
            dsimp [areaDet]; ring
        _ = 0 := by rw [hB, hC]; ring
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hy)
  · have hprod : (u.re-v.re) * areaDet a b c = 0 := by
      calc
        _ = ((b.re-a.re)*(u.re-v.re) + (b.im-a.im)*(u.im-v.im))*(c.im-a.im) -
          ((c.re-a.re)*(u.re-v.re) + (c.im-a.im)*(u.im-v.im))*(b.im-a.im) := by
            dsimp [areaDet]; ring
        _ = 0 := by rw [hB, hC]; ring
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hx)

/-- In general position, one fixed pair can have at most two equidistant centers. -/
theorem equidistant_centers_le_two {S : Finset ℂ} (hS : NoThreeCollinear S)
    {u v : ℂ} (huv : u ≠ v) :
    (S.filter (fun p => sqDist p u = sqDist p v)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < (S.filter (fun p => sqDist p u = sqDist p v)).card)
  exact hS a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 c (mem_filter.mp hc).1
    hab hac hbc (equidistant_centers_collinear huv
      (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2)

def bendX (t x : ℝ) : ℂ := ⟨x, t*x^2⟩
def bendY (t y : ℝ) : ℂ := ⟨t*y^2, y⟩

/-- Bending both axes destroys the cross-axis reflected-pair equalities. -/
theorem bent_cross_difference (t x y : ℝ) :
    sqDist (bendX t x) (bendY t y) - sqDist (bendX t x) (bendY t (-y)) =
      -4*t*x^2*y := by
  dsimp [sqDist, bendX, bendY]
  ring

theorem bending_breaks_cross_pair {t x y : ℝ} (ht : t ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) : sqDist (bendX t x) (bendY t y) ≠
      sqDist (bendX t x) (bendY t (-y)) := by
  intro h
  have he := bent_cross_difference t x y
  rw [h, sub_self] at he
  have hn : -4*t*x^2*y ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht) (pow_ne_zero 2 hx)) hy
  exact hn he.symm

theorem distance_eq_of_sqDist_eq {p q z : ℂ} (h : sqDist p z = sqDist q z) :
    dist p z = dist q z := by
  rw [sqDist_eq_dist_sq, sqDist_eq_dist_sq] at h
  nlinarith [dist_nonneg (x := p) (y := z), dist_nonneg (x := q) (y := z)]

/-- Any two opposite pairs on one of the bent axes lie on a common circle. -/
theorem bent_symmetric_circle {t : ℝ} (ht : t ≠ 0) (a b : ℝ) :
    ∃ z : ℂ, ∃ r : ℝ, dist (bendX t a) z = r ∧ dist (bendX t (-a)) z = r ∧
      dist (bendX t b) z = r ∧ dist (bendX t (-b)) z = r := by
  let k : ℝ := (1 + t^2*(a^2+b^2))/(2*t)
  let z : ℂ := ⟨0,k⟩
  have hk : 2*t*k = 1+t^2*(a^2+b^2) := by
    dsimp [k]
    field_simp
  have hab : sqDist (bendX t a) z = sqDist (bendX t b) z := by
    apply sub_eq_zero.mp
    calc
      _ = (a^2-b^2)*(1+t^2*(a^2+b^2)-2*t*k) := by dsimp [sqDist,bendX,z]; ring
      _ = 0 := by rw [hk]; ring
  have hneg (x : ℝ) : sqDist (bendX t (-x)) z = sqDist (bendX t x) z := by
    dsimp [sqDist,bendX,z]; ring
  exact ⟨z, dist (bendX t a) z, rfl, distance_eq_of_sqDist_eq (hneg a),
    distance_eq_of_sqDist_eq hab.symm, distance_eq_of_sqDist_eq ((hneg b).trans hab.symm)⟩

def fourBentPoints (t : ℝ) : Finset ℂ :=
  {bendX t 2, bendX t (-2), bendX t 4, bendX t (-4)}

/-- The natural quadratic bending fails the no-four-concyclic condition for every t != 0. -/
theorem quadratic_bending_not_no_four {t : ℝ} (ht : t ≠ 0) :
    ¬ NoFourConcyclic (fourBentPoints t) := by
  classical
  obtain ⟨z, r, h1, h2, h3, h4⟩ := bent_symmetric_circle ht 2 4
  intro hS
  have hf : (fourBentPoints t).filter (fun p => dist p z = r) = fourBentPoints t := by
    apply filter_eq_self.mpr
    intro p hp
    simp only [fourBentPoints, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hc : (fourBentPoints t).card = 4 := by
    norm_num [fourBentPoints, bendX, Complex.ext_iff]
  have h := hS z r
  rw [hf, hc] at h
  omega

end
end JSP000530.Research
