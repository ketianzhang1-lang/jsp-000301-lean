import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# JSP-000530 / Erdős 654: the two-axis counterexample

The two-axis construction is due to Aletheia, reported by Feng et al.,
arXiv:2601.22401v3, Section 3.1. This independently written formalization
uses even and odd coordinates in place of powers of two and three.
It concerns the version allowing three collinear points.
-/

namespace JSP000530
open Finset

abbrev Vertex (m : ℕ) := Bool × Bool × Fin m

def magnitude (axis : Bool) (k : ℕ) : ℤ :=
  if axis then 2 * k + 1 else 2 * (k + 1)

def coordinate (axis sign : Bool) (k : ℕ) : ℤ :=
  if sign then magnitude axis k else -magnitude axis k

def point {m : ℕ} (v : Vertex m) : ℂ :=
  if v.1 then ⟨0, coordinate v.1 v.2.1 v.2.2⟩
  else ⟨coordinate v.1 v.2.1 v.2.2, 0⟩

lemma magnitude_pos (axis : Bool) (k : ℕ) : 0 < magnitude axis k := by
  cases axis <;> simp only [magnitude, Bool.false_eq_true, ite_false, ite_true] <;> omega

lemma coordinate_ne_zero (axis sign : Bool) (k : ℕ) : coordinate axis sign k ≠ 0 := by
  have := magnitude_pos axis k
  cases sign <;> simp_all [coordinate] <;> omega

lemma coordinate_injective (axis : Bool) :
    Function.Injective (fun v : Bool × ℕ => coordinate axis v.1 v.2) := by
  rintro ⟨s, k⟩ ⟨t, l⟩ h
  cases axis <;> cases s <;> cases t <;>
    simp_all [coordinate, magnitude] <;> omega

lemma point_injective (m : ℕ) : Function.Injective (@point m) := by
  rintro ⟨a, s, k⟩ ⟨b, t, l⟩ h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  cases a <;> cases b <;> simp only [point, Bool.false_eq_true, ite_false, ite_true] at hr hi
  · have he : (s, (k : ℕ)) = (t, (l : ℕ)) := coordinate_injective false (by
      exact_mod_cast hr)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, hk⟩ := he
    have : k = l := Fin.ext hk
    subst l
    rfl
  · exact ((coordinate_ne_zero false s k) (by exact_mod_cast hr)).elim
  · exact ((coordinate_ne_zero true s k) (by exact_mod_cast hi)).elim
  · have he : (s, (k : ℕ)) = (t, (l : ℕ)) := coordinate_injective true (by
      exact_mod_cast hi)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, hk⟩ := he
    have : k = l := Fin.ext hk
    subst l
    rfl

lemma even_odd_products_ne (s t u v : Bool) (i j k l : ℕ) :
    coordinate false s i * coordinate false t j ≠
      coordinate true u k * coordinate true v l := by
  cases s <;> cases t <;> cases u <;> cases v <;>
    simp only [coordinate, magnitude, Bool.false_eq_true, ite_false, ite_true]
    <;> intro h <;> ring_nf at h <;> omega

def sqDist (z w : ℂ) : ℝ := (z.re - w.re)^2 + (z.im - w.im)^2

lemma sqDist_eq_dist_sq (z w : ℂ) : sqDist z w = dist z w ^ 2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq]
  simp [sqDist, Complex.normSq_apply, pow_two]

lemma circle_axis_three (a b c x y r : ℝ)
    (ha : (a-x)^2 + y^2 = r) (hb : (b-x)^2 + y^2 = r)
    (hc : (c-x)^2 + y^2 = r) : a = b ∨ a = c ∨ b = c := by
  by_contra h
  push Not at h
  have hab : a+b=2*x := by
    have : (a-b)*(a+b-2*x)=0 := by nlinarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact (h.1 (sub_eq_zero.mp h')).elim
    · linarith
  have hac : a+c=2*x := by
    have : (a-c)*(a+c-2*x)=0 := by nlinarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact (h.2.1 (sub_eq_zero.mp h')).elim
    · linarith
  exact h.2.2 (by linarith)

lemma circle_axis_two_two (a b c d x y r : ℝ) (hab : a ≠ b) (hcd : c ≠ d)
    (ha : (a-x)^2 + y^2 = r) (hb : (b-x)^2 + y^2 = r)
    (hc : x^2 + (c-y)^2 = r) (hd : x^2 + (d-y)^2 = r) : a*b = c*d := by
  have h₁ : a+b=2*x := by
    have : (a-b)*(a+b-2*x)=0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact (hab (sub_eq_zero.mp h)).elim
    · linarith
  have h₂ : c+d=2*y := by
    have : (c-d)*(c+d-2*y)=0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact (hcd (sub_eq_zero.mp h)).elim
    · linarith
  nlinarith [congrArg (fun t : ℝ => a*t) h₁, congrArg (fun t : ℝ => c*t) h₂]

lemma coordinate_eq_point_eq {m : ℕ} (axis : Bool) (u v : Bool × Fin m)
    (h : (coordinate axis u.1 u.2 : ℝ) = coordinate axis v.1 v.2) :
    point (axis, u) = point (axis, v) := by
  cases axis <;> apply Complex.ext <;> simp_all [point]

lemma circle_three {m : ℕ} (axis : Bool) (u v w : Bool × Fin m) (z : ℂ) (r : ℝ)
    (hu : sqDist (point (axis,u)) z = r)
    (hv : sqDist (point (axis,v)) z = r)
    (hw : sqDist (point (axis,w)) z = r) :
    point (axis,u) = point (axis,v) ∨ point (axis,u) = point (axis,w) ∨
      point (axis,v) = point (axis,w) := by
  have h : (coordinate axis u.1 u.2 : ℝ) = coordinate axis v.1 v.2 ∨
      (coordinate axis u.1 u.2 : ℝ) = coordinate axis w.1 w.2 ∨
      (coordinate axis v.1 v.2 : ℝ) = coordinate axis w.1 w.2 := by
    cases axis
    · exact circle_axis_three _ _ _ z.re z.im r
        (by simpa [sqDist,point] using hu) (by simpa [sqDist,point] using hv)
        (by simpa [sqDist,point] using hw)
    · exact circle_axis_three _ _ _ z.im z.re r
        (by simpa [sqDist,point,add_comm] using hu)
        (by simpa [sqDist,point,add_comm] using hv)
        (by simpa [sqDist,point,add_comm] using hw)
  rcases h with h | h | h
  · exact Or.inl (coordinate_eq_point_eq _ _ _ h)
  · exact Or.inr (Or.inl (coordinate_eq_point_eq _ _ _ h))
  · exact Or.inr (Or.inr (coordinate_eq_point_eq _ _ _ h))

lemma circle_four_mixed {m : ℕ} (u v w t : Bool × Fin m) (z : ℂ) (r : ℝ)
    (huv : point (false,u) ≠ point (false,v))
    (hwt : point (true,w) ≠ point (true,t))
    (hu : sqDist (point (false,u)) z = r)
    (hv : sqDist (point (false,v)) z = r)
    (hw : sqDist (point (true,w)) z = r)
    (ht : sqDist (point (true,t)) z = r) : False := by
  have h := circle_axis_two_two
    (coordinate false u.1 u.2) (coordinate false v.1 v.2)
    (coordinate true w.1 w.2) (coordinate true t.1 t.2) z.re z.im r
    (fun h => huv (coordinate_eq_point_eq _ _ _ h))
    (fun h => hwt (coordinate_eq_point_eq _ _ _ h))
    (by simpa [sqDist,point] using hu) (by simpa [sqDist,point] using hv)
    (by simpa [sqDist,point] using hw) (by simpa [sqDist,point] using ht)
  exact even_odd_products_ne u.1 v.1 w.1 t.1 u.2 v.2 w.2 t.2 (by exact_mod_cast h)

lemma no_four_on_circle {m : ℕ} (a b c d : Vertex m) (z : ℂ) (r : ℝ)
    (hab : point a ≠ point b) (hac : point a ≠ point c) (had : point a ≠ point d)
    (hbc : point b ≠ point c) (hbd : point b ≠ point d) (hcd : point c ≠ point d)
    (ha : sqDist (point a) z = r) (hb : sqDist (point b) z = r)
    (hc : sqDist (point c) z = r) (hd : sqDist (point d) z = r) : False := by
  rcases a with ⟨a,u⟩
  rcases b with ⟨b,v⟩
  rcases c with ⟨c,w⟩
  rcases d with ⟨d,t⟩
  cases a <;> cases b <;> cases c <;> cases d
  · rcases circle_three false u v w z r ha hb hc with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h
  · rcases circle_three false u v w z r ha hb hc with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h
  · rcases circle_three false u v t z r ha hb hd with h | h | h
    · exact hab h
    · exact had h
    · exact hbd h
  · exact circle_four_mixed u v w t z r hab hcd ha hb hc hd
  · rcases circle_three false u w t z r ha hc hd with h | h | h
    · exact hac h
    · exact had h
    · exact hcd h
  · exact circle_four_mixed u w v t z r hac hbd ha hc hb hd
  · exact circle_four_mixed u t v w z r had hbc ha hd hb hc
  · rcases circle_three true v w t z r hb hc hd with h | h | h
    · exact hbc h
    · exact hbd h
    · exact hcd h
  · rcases circle_three false v w t z r hb hc hd with h | h | h
    · exact hbc h
    · exact hbd h
    · exact hcd h
  · exact circle_four_mixed v w u t z r hbc had hb hc ha hd
  · exact circle_four_mixed v t u w z r hbd hac hb hd ha hc
  · rcases circle_three true u w t z r ha hc hd with h | h | h
    · exact hac h
    · exact had h
    · exact hcd h
  · exact circle_four_mixed w t u v z r hcd hab hc hd ha hb
  · rcases circle_three true u v t z r ha hb hd with h | h | h
    · exact hab h
    · exact had h
    · exact hbd h
  · rcases circle_three true u v w z r ha hb hc with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h
  · rcases circle_three true u v w z r ha hb hc with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h

noncomputable def configuration (m : ℕ) : Finset ℂ := by
  classical
  exact Finset.univ.image (@point m)

theorem configuration_card (m : ℕ) : (configuration m).card = 4*m := by
  classical
  rw [configuration, Finset.card_image_of_injective _ (point_injective m)]
  simp [Vertex]
  omega

/-- Every Euclidean circle contains at most three constructed points. -/
theorem configuration_circle_bound (m : ℕ) (z : ℂ) (r : ℝ) :
    ((configuration m).filter (fun p => dist p z = r)).card ≤ 3 := by
  classical
  by_contra h
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd⟩ :=
    Finset.three_lt_card_iff.mp (Nat.lt_of_not_ge h)
  obtain ⟨ham,har⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbm,hbr⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcm,hcr⟩ := Finset.mem_filter.mp hc
  obtain ⟨hdm,hdr⟩ := Finset.mem_filter.mp hd
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ham
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hbm
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hcm
  obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hdm
  exact no_four_on_circle a b c d z (r^2) hab hac had hbc hbd hcd
    (by rw [sqDist_eq_dist_sq,har]) (by rw [sqDist_eq_dist_sq,hbr])
    (by rw [sqDist_eq_dist_sq,hcr]) (by rw [sqDist_eq_dist_sq,hdr])

lemma opposite_sign_dist {m : ℕ} (axis : Bool) (u : Bool × Fin m)
    (sign : Bool) (k : Fin m) :
    dist (point (axis,u)) (point (!axis,sign,k)) =
      dist (point (axis,u)) (point (!axis,true,k)) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [← sqDist_eq_dist_sq, ← sqDist_eq_dist_sq]
  cases axis <;> cases sign <;> simp [sqDist,point,coordinate]

/-- Counting zero as a distance, every point sees at most 3m distance values. -/
theorem configuration_distance_bound {m : ℕ} (v : Vertex m) :
    ((configuration m).image (dist (point v))).card ≤ 3*m := by
  classical
  rcases v with ⟨axis,u⟩
  let same : Finset ℝ := Finset.univ.image
    (fun p : Bool × Fin m => dist (point (axis,u)) (point (axis,p)))
  let cross : Finset ℝ := Finset.univ.image
    (fun k : Fin m => dist (point (axis,u)) (point (!axis,true,k)))
  have hsub : (configuration m).image (dist (point (axis,u))) ⊆ same ∪ cross := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨b,s,k⟩,_,rfl⟩ := Finset.mem_image.mp hp
    by_cases h : b = axis
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(s,k), Finset.mem_univ _, by simp [h]⟩
    · have hb : b = !axis := by cases b <;> cases axis <;> simp_all
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, by
        rw [hb]
        exact (opposite_sign_dist axis u s k).symm⟩
  have hsame : same.card ≤ 2*m := by
    exact (Finset.card_image_le).trans_eq (by simp)
  have hcross : cross.card ≤ m := by
    exact (Finset.card_image_le).trans_eq (by simp)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

noncomputable def distanceValues (S : Finset ℂ) (p : ℂ) : Finset ℝ := by
  classical
  exact (S.erase p).image (dist p)

def NoFourConcyclic (S : Finset ℂ) : Prop := by
  classical
  exact ∀ (z : ℂ) (r : ℝ), (S.filter (fun p => dist p z = r)).card ≤ 3

/-- The usual count excludes the base point; the resulting bound is 3m-1. -/
theorem configuration_distance_bound_strict {m : ℕ} {p : ℂ} (hp : p ∈ configuration m) :
    (distanceValues (configuration m) p).card < 3*m := by
  classical
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hp
  have h := configuration_distance_bound v
  have hp : point v ∈ configuration m := Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hn : (0 : ℝ) ∉ distanceValues (configuration m) (point v) := by
    intro h0
    obtain ⟨q,hq,hq0⟩ := Finset.mem_image.mp h0
    exact (Finset.mem_erase.mp hq).1 (dist_eq_zero.mp hq0).symm
  have he : (configuration m).image (dist (point v)) =
      insert 0 (distanceValues (configuration m) (point v)) := by
    unfold distanceValues
    rw [← dist_self (point v), ← Finset.image_insert, Finset.insert_erase hp]
  rw [he, Finset.card_insert_of_notMem hn] at h
  omega

/-- Arbitrarily large, genuine planar configurations with the required obstruction. -/
theorem counterexample_family (m : ℕ) :
    ∃ S : Finset ℂ, S.card = 4*m ∧ NoFourConcyclic S ∧
      ∀ p ∈ S, (distanceValues S p).card < 3*m := by
  exact ⟨configuration m, configuration_card m,
    configuration_circle_bound m, fun _ hp => configuration_distance_bound_strict hp⟩

/-- The no-four-on-a-circle hypothesis alone does not force (1-o(1))n pinned distances. -/
theorem not_asymptotically_all_distances :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : Finset ℂ,
      N ≤ S.card → NoFourConcyclic S →
        ∃ p ∈ S, (1-ε)*(S.card : ℝ) ≤ (distanceValues S p).card) := by
  intro h
  obtain ⟨N,hN⟩ := h (1/8) (by norm_num)
  obtain ⟨S,hcard,hcircle,hbound⟩ := counterexample_family (N+1)
  obtain ⟨p,hp,hpbound⟩ := hN S (by omega) hcircle
  have hb : ((distanceValues S p).card : ℝ) < 3*((N : ℝ)+1) := by
    exact_mod_cast hbound p hp
  have hc : (S.card : ℝ) = 4*((N : ℝ)+1) := by exact_mod_cast hcard
  rw [hc] at hpbound
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end JSP000530
