import Core
namespace JSP000780General
open Finset

def odds (r : ℕ) : Finset ℕ := (range (r+1)).filter Odd

def ordinary (r : ℕ) : Finset (ℕ × ℕ) :=
  ((odds r).erase 3).image (fun j => (j, 2 * r.choose j))

def splitPairs (r : ℕ) : Finset (ℕ × ℕ) :=
  (splitCoeffs r).image (fun c => (3, c))

def coefficients (r : ℕ) : Finset (ℕ × ℕ) := ordinary r ∪ splitPairs r

lemma three_mem_odds (r : ℕ) (hr : 6 ≤ r) : 3 ∈ odds r := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by decide⟩

lemma coeff_disjoint (r : ℕ) : Disjoint (ordinary r) (splitPairs r) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hb
  have hj3 := (Finset.mem_erase.mp hj).1
  exact hj3 (by simpa using (congrArg Prod.fst he).symm)

lemma coefficients_card (r : ℕ) (hr : 6 ≤ r) : (coefficients r).card = r-3 := by
  rw [coefficients, Finset.card_union_of_disjoint (coeff_disjoint r)]
  have hi : Function.Injective (fun j : ℕ => (j, 2*r.choose j)) := by
    intro a b h; exact congrArg Prod.fst h
  have hi' : Function.Injective (fun c : ℕ => (3, c)) := by
    intro a b h; exact congrArg Prod.snd h
  rw [ordinary, splitPairs, Finset.card_image_of_injective _ hi,
    Finset.card_image_of_injective _ hi', Finset.card_erase_of_mem (three_mem_odds r hr),
    splitCoeffs_card r hr]
  have h := odds_card r
  change (odds r).card = (r+1)/2 at h
  rw [h]
  unfold splitCount
  omega

lemma coefficient_bounds (r : ℕ) (hr : 6 ≤ r) (a : ℕ × ℕ)
    (ha : a ∈ coefficients r) : 0 < a.1 ∧ a.1 ≤ r ∧ 0 < a.2 ∧ a.2 ≤ 2^(r+1) := by
  have hpw (j : ℕ) : 2 * r.choose j ≤ 2^(r+1) := by
    have h := choose_le_two_pow r j
    rw [pow_succ]; omega
  rcases Finset.mem_union.mp ha with h | h
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hjo := Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)
    have hjr : j ≤ r := by have := Finset.mem_range.mp hjo.1; omega
    exact ⟨hjo.2.pos, hjr, Nat.mul_pos (by omega) (Nat.choose_pos hjr), hpw j⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
    have hcb := splitCoeffs_bounds r c hr hc
    exact ⟨by omega, by omega, hcb.1, hcb.2.trans (hpw 3)⟩

lemma first_coefficient (r : ℕ) (hr : 6 ≤ r) : (1, 2*r) ∈ coefficients r := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨1, ?_, by simp⟩
  simp [odds]; omega

lemma coefficient_sum (r : ℕ) (hr : 6 ≤ r) (g : ℕ → ℕ) :
    (∑ a ∈ coefficients r, a.2 * g a.1) = ∑ j ∈ odds r, 2*r.choose j*g j := by
  rw [coefficients, Finset.sum_union (coeff_disjoint r)]
  have hi : ∀ a ∈ (odds r).erase 3, ∀ b ∈ (odds r).erase 3,
      (a,2*r.choose a) = (b,2*r.choose b) → a=b := by
    intro a ha b hb h; exact congrArg Prod.fst h
  have hi' : ∀ a ∈ splitCoeffs r, ∀ b ∈ splitCoeffs r,
      (3,a) = (3,b) → a=b := by
    intro a ha b hb h; exact congrArg Prod.snd h
  rw [ordinary, splitPairs, Finset.sum_image hi, Finset.sum_image hi']
  simp only
  rw [← Finset.sum_mul, splitCoeffs_sum r hr]
  exact Finset.sum_erase_add _ _ (three_mem_odds r hr)

lemma split_binomial (r x y : ℕ) (hr : 6 ≤ r) (hxy : y ≤ x) :
    (x-y)^r + ∑ a ∈ coefficients r, a.2*x^(r-a.1)*y^a.1 = (x+y)^r := by
  have hc := coefficient_sum r hr (fun j => x^(r-j)*y^j)
  simp only [← mul_assoc] at hc
  rw [hc]
  exact binomial_odd_nat r x y hxy

/-- A small explicit modulus, avoiding a factorial of exponential size. -/
def modulus (r : ℕ) : ℕ := ∏ a ∈ coefficients r, a.2

lemma modulus_pos (r : ℕ) (hr : 6 ≤ r) : 0 < modulus r := by
  apply Finset.prod_pos
  intro a ha
  exact (coefficient_bounds r hr a ha).2.2.1

lemma coefficient_dvd_modulus (r : ℕ) (a : ℕ × ℕ) (ha : a ∈ coefficients r) :
    a.2 ∣ modulus r := Finset.dvd_prod_of_mem _ ha

end JSP000780General
