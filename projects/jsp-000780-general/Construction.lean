import Coefficients
import Separation
import Mathlib.Data.Set.Finite.Basic
namespace JSP000780General
open Finset

def cap (r : ℕ) : ℕ := 2^(r+1)
def scale (r : ℕ) : ℕ := 2^r * cap r + 2
def parameter (r t : ℕ) : ℕ := modulus r * (scale r + t) + 1

def xval (r t : ℕ) : ℕ := (parameter r t)^r
def yval (r : ℕ) : ℕ := (modulus r)^r

def monomial (r x y : ℕ) (a : ℕ × ℕ) : ℕ := a.2 * x^(r-a.1) * y^a.1

def terms (r t : ℕ) : Finset ℕ :=
  insert ((xval r t - yval r)^r)
    ((coefficients r).image (monomial r (xval r t) (yval r)))

def total (r t : ℕ) : ℕ := (xval r t + yval r)^r

lemma parameter_coprime (r t : ℕ) : (parameter r t).Coprime (modulus r) := by
  unfold parameter
  rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left _

lemma parameter_large (r t : ℕ) (hr : 6 ≤ r) :
    scale r * yval r < xval r t := by
  have hp : scale r * modulus r < parameter r t := by
    unfold parameter; nlinarith
  have hs : scale r ≤ (scale r)^r := Nat.le_self_pow (by omega) _
  calc
    _ ≤ (scale r)^r * (modulus r)^r := Nat.mul_le_mul_right _ hs
    _ = (scale r * modulus r)^r := (mul_pow ..).symm
    _ < _ := Nat.pow_lt_pow_left hp (by omega)

lemma scale_bounds (r t : ℕ) (hr : 6 ≤ r) :
    0 < yval r ∧ 0 < cap r ∧ cap r * yval r < xval r t ∧
    2^r * cap r * yval r < xval r t ∧ 2*yval r ≤ xval r t := by
  have hy : 0 < yval r := Nat.pow_pos (modulus_pos r hr)
  have hK : 0 < cap r := by unfold cap; positivity
  have hp : 0 < 2^r := by positivity
  have hl := parameter_large r t hr
  unfold scale at hl
  have hn : 0 ≤ 2^r * cap r * yval r := Nat.zero_le _
  refine ⟨hy, hK, ?_, ?_, ?_⟩ <;> nlinarith

lemma monomial_pos (r x y : ℕ) (hr : 6 ≤ r) (hx : 0 < x) (hy : 0 < y)
    (a : ℕ × ℕ) (ha : a ∈ coefficients r) : 0 < monomial r x y a := by
  have hc := (coefficient_bounds r hr a ha).2.2.1
  unfold monomial
  positivity

lemma monomial_inj (r x y : ℕ) (hr : 6 ≤ r) (hy : 0 < y)
    (hxy : cap r * y < x) : Set.InjOn (monomial r x y) (coefficients r) := by
  intro a ha b hb he
  have hA := coefficient_bounds r hr a ha
  have hB := coefficient_bounds r hr b hb
  have hK : 0 < cap r := by unfold cap; positivity
  have hfst : a.1 = b.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have ht := monomial_strict hy hxy hK h hB.2.1 hA.2.2.1 hB.2.2.2
      exact (ne_of_lt ht) he.symm
    · have ht := monomial_strict hy hxy hK h hA.2.1 hB.2.2.1 hA.2.2.2
      exact (ne_of_lt ht) he
  apply Prod.ext hfst
  have hx : 0 < x := by omega
  have hfac : 0 < x^(r-a.1)*y^a.1 := by positivity
  unfold monomial at he
  rw [← hfst] at he
  have he' : a.2*(x^(r-a.1)*y^a.1) = b.2*(x^(r-a.1)*y^a.1) := by
    simpa [mul_assoc] using he
  exact Nat.eq_of_mul_eq_mul_right hfac he'

lemma first_not_mem (r t : ℕ) (hr : 6 ≤ r) :
    (xval r t-yval r)^r ∉
      (coefficients r).image (monomial r (xval r t) (yval r)) := by
  intro h
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
  have hs := scale_bounds r t hr
  have hb := coefficient_bounds r hr a ha
  have hbound := monomial_bound (show yval r ≤ xval r t by omega) hb.1 hb.2.1 hb.2.2.2
  have hdom := first_dominates (show 0 < r by omega) hs.2.2.2.1 hs.2.2.2.2
  exact (ne_of_lt (hbound.trans_lt hdom)) he

lemma terms_card (r t : ℕ) (hr : 6 ≤ r) : (terms r t).card = r-2 := by
  have hs := scale_bounds r t hr
  rw [terms, Finset.card_insert_of_notMem (first_not_mem r t hr),
    Finset.card_image_of_injOn (monomial_inj _ _ _ hr hs.1 hs.2.2.1), coefficients_card r hr]
  omega

lemma terms_sum (r t : ℕ) (hr : 6 ≤ r) : ∑ n ∈ terms r t, n = total r t := by
  have hs := scale_bounds r t hr
  rw [terms, Finset.sum_insert (first_not_mem r t hr),
    Finset.sum_image (monomial_inj _ _ _ hr hs.1 hs.2.2.1)]
  exact split_binomial _ _ _ hr (by omega)

lemma terms_positive (r t n : ℕ) (hr : 6 ≤ r) (hn : n ∈ terms r t) : 0 < n := by
  have hs := scale_bounds r t hr
  rcases Finset.mem_insert.mp hn with h | h
  · subst n
    exact Nat.pow_pos (Nat.sub_pos_of_lt (by omega))
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact monomial_pos _ _ _ hr (by omega) hs.1 a ha

lemma terms_full (r t n : ℕ) (hr : 6 ≤ r) (hn : n ∈ terms r t) : Full r n := by
  rcases Finset.mem_insert.mp hn with h | h
  · subst n
    exact full_pow _ _
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    apply monomial_full (coefficient_bounds r hr a ha).1
    intro p _hp hd
    exact hd.trans (coefficient_dvd_modulus r a ha)

lemma total_full (r t : ℕ) : Full r (total r t) := full_pow _ _

end JSP000780General
