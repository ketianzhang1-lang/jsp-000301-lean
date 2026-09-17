import Construction
namespace JSP000780General
open Finset

lemma first_two_coprime (r t : ℕ) (hr : 6 ≤ r) :
    ((xval r t-yval r)^r).Coprime
      (monomial r (xval r t) (yval r) (1,2*r)) := by
  have hs := scale_bounds r t hr
  have hle : yval r ≤ xval r t := by omega
  have hc : (xval r t).Coprime (yval r) := (parameter_coprime r t).pow r r
  have hy : (xval r t-yval r).Coprime (yval r) :=
    (Nat.coprime_sub_self_left hle).mpr hc
  have hx : (xval r t-yval r).Coprime (xval r t) :=
    (Nat.coprime_self_sub_left hle).mpr hc.symm
  have hd : 2*r ∣ yval r :=
    (coefficient_dvd_modulus r (1,2*r) (first_coefficient r hr)).trans
      (dvd_pow_self _ (by omega))
  have hcoef : (xval r t-yval r).Coprime (2*r) := hy.of_dvd_right hd
  simpa [monomial] using ((hcoef.mul_right (hx.pow_right (r-1))).mul_right hy).pow_left r

lemma terms_gcd (r t : ℕ) (hr : 6 ≤ r) : (terms r t).gcd id = 1 := by
  have h1 : (xval r t-yval r)^r ∈ terms r t := Finset.mem_insert_self _ _
  have h2 : monomial r (xval r t) (yval r) (1,2*r) ∈ terms r t := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(1,2*r), first_coefficient r hr, rfl⟩
  apply Nat.dvd_one.mp
  rw [← (first_two_coprime r t hr).gcd_eq_one]
  exact Nat.dvd_gcd (Finset.gcd_dvd h1) (Finset.gcd_dvd h2)

lemma parameter_strict (r : ℕ) (hr : 6 ≤ r) : StrictMono (parameter r) := by
  intro a b hab
  have hB := modulus_pos r hr
  unfold parameter
  nlinarith

lemma total_strict (r : ℕ) (hr : 6 ≤ r) : StrictMono (total r) := by
  intro a b hab
  apply Nat.pow_lt_pow_left _ (by omega)
  apply Nat.add_lt_add_right
  exact Nat.pow_lt_pow_left (parameter_strict r hr hab) (by omega)

lemma terms_injective (r : ℕ) (hr : 6 ≤ r) : Function.Injective (terms r) := by
  intro a b he
  apply (total_strict r hr).injective
  rw [← terms_sum r a hr, ← terms_sum r b hr, he]

/-- The original set-valued target uses collective gcd, not pairwise coprimality. -/
def Solutions (r : ℕ) : Set (Finset ℕ) :=
  {s | s.card = r-2 ∧ s.gcd id = 1 ∧ Full r (∑ n ∈ s, n) ∧
    ∀ n ∈ s, 0 < n ∧ Full r n}

theorem solution_for_every_parameter (r t : ℕ) (hr : 6 ≤ r) : terms r t ∈ Solutions r := by
  refine ⟨terms_card r t hr, terms_gcd r t hr, ?_, ?_⟩
  · rw [terms_sum r t hr]
    exact total_full r t
  · intro n hn
    exact ⟨terms_positive r t n hr hn, terms_full r t n hr hn⟩

/-- All exponents r >= 6, with an explicit composite-allowed arithmetic-progression parameter. -/
theorem infinitely_many_solutions : ∀ r ≥ 6, (Solutions r).Infinite := by
  intro r hr
  apply (Set.infinite_range_of_injective (terms_injective r hr)).mono
  rintro s ⟨t, rfl⟩
  exact solution_for_every_parameter r t hr

theorem infinitely_many_totals (r : ℕ) (hr : 6 ≤ r) :
    {n : ℕ | ∃ s ∈ Solutions r, ∑ k ∈ s, k = n}.Infinite := by
  apply (Set.infinite_range_of_injective (total_strict r hr).injective).mono
  rintro n ⟨t, rfl⟩
  exact ⟨terms r t, solution_for_every_parameter r t hr, terms_sum r t hr⟩

end JSP000780General
