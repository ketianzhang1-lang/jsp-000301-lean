import JSP912.Potential

namespace JSP912

/-- All positive divisors, in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ := (Nat.divisors n).sort (· ≤ ·)

/-- The sum over every consecutive pair in the complete ordered divisor list. -/
noncomputable def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).map (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum

lemma mem_sortedDivisors {n d : ℕ} (hn : 0 < n) :
    d ∈ sortedDivisors n ↔ d ∣ n := by
  simp [sortedDivisors, Nat.mem_divisors, hn.ne']

lemma sortedDivisors_strict (n : ℕ) : (sortedDivisors n).Pairwise (· < ·) :=
  Finset.sort_sorted_lt (Nat.divisors n)

lemma sortedDivisors_get_le (n i j : ℕ)
    (hi : i < (sortedDivisors n).length) (hj : j < (sortedDivisors n).length)
    (hij : i ≤ j) : (sortedDivisors n)[i] ≤ (sortedDivisors n)[j] := by
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst j
    rfl
  · exact (List.pairwise_iff_getElem.mp (sortedDivisors_strict n) i j hi hj hlt).le

lemma sortedDivisors_neighbors (n i : ℕ) (hn : 0 < n)
    (hi : i + 1 < (sortedDivisors n).length) :
    Consecutive n (sortedDivisors n)[i] (sortedDivisors n)[i + 1] := by
  have hi0 : i < (sortedDivisors n).length := by omega
  have haD : (sortedDivisors n)[i] ∣ n :=
    (mem_sortedDivisors hn).mp (List.getElem_mem hi0)
  have hbD : (sortedDivisors n)[i + 1] ∣ n :=
    (mem_sortedDivisors hn).mp (List.getElem_mem hi)
  have hab := List.pairwise_iff_getElem.mp (sortedDivisors_strict n) i (i + 1) hi0 hi (by omega)
  refine ⟨Nat.pos_of_dvd_of_pos haD hn, hab, haD, hbD, ?_⟩
  intro d hd had hdb
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp ((mem_sortedDivisors hn).mpr hd)
  by_cases hji : j ≤ i
  · have hh := sortedDivisors_get_le n j i hj hi0 hji
    rw [hjeq] at hh
    omega
  · have hh := sortedDivisors_get_le n (i + 1) j hi hj (by omega)
    rw [hjeq] at hh
    omega

lemma sortedDivisors_zip_consecutive {n a b : ℕ} (hn : 0 < n)
    (hp : (a, b) ∈ (sortedDivisors n).zip (sortedDivisors n).tail) :
    Consecutive n a b := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp
  have hil : i + 1 < (sortedDivisors n).length := by
    simp only [List.length_zip, List.length_tail] at hi
    omega
  have hae := congrArg Prod.fst heq
  have hbe := congrArg Prod.snd heq
  simp only [List.getElem_zip, Prod.fst, Prod.snd, List.getElem_tail] at hae hbe
  have hh := sortedDivisors_neighbors n i hn hil
  rw [hae, hbe] at hh
  exact hh

lemma potential_sum_telescope (Φ : ℕ → ℝ) (C : ℝ) (a : ℕ) (l : List ℕ) :
    (((a :: l).zip l).map (fun p => C * (Φ p.1 - Φ p.2))).sum =
      C * (Φ a - Φ ((a :: l).getLast (by simp))) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.getLast_cons_cons]
    rw [ih b]
    ring

lemma potential_sum_le (Φ : ℕ → ℝ) (C : ℝ) (l : List ℕ) (hC : 0 ≤ C)
    (hbounds : ∀ d ∈ l, -1 ≤ Φ d ∧ Φ d ≤ 1) :
    ((l.zip l.tail).map (fun p => C * (Φ p.1 - Φ p.2))).sum ≤ 2 * C := by
  cases l with
  | nil => simp; positivity
  | cons a l =>
    simp only [List.tail_cons]
    rw [potential_sum_telescope]
    have ha := hbounds a (by simp)
    have hb := hbounds ((a :: l).getLast (by simp)) (List.getLast_mem (by simp))
    have hd : Φ a - Φ ((a :: l).getLast (by simp)) ≤ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hd hC]

/-- Explicit full-scope bound, uniform in the unbounded construction parameter K. -/
theorem hAlpha_candidate_bound (α : ℝ) (r K : ℕ) (hα : 1 < α)
    (hr : 4 ≤ (r : ℝ) * (α - 1)) :
    hAlpha α (candidate r K) ≤ 64 * (scaleConstant r : ℝ) ^ 2 := by
  have hn := candidate_pos r K
  have hcost : ∀ p ∈ (sortedDivisors (candidate r K)).zip (sortedDivisors (candidate r K)).tail,
      ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α ≤
        (32 * (scaleConstant r : ℝ) ^ 2) *
          (divisorPotential (candidate r K) p.1 - divisorPotential (candidate r K) p.2) := by
    intro p hp
    have hh := all_gap_cost r K p.1 p.2 (α - 1) (by linarith) hr
      (sortedDivisors_zip_consecutive hn hp)
    simpa only [sub_add_cancel] using hh
  have hs := List.sum_le_sum hcost
  have ht := potential_sum_le (divisorPotential (candidate r K))
    (32 * (scaleConstant r : ℝ) ^ 2) (sortedDivisors (candidate r K)) (by positivity)
    (fun d hd => divisorPotential_bounds hn ((mem_sortedDivisors hn).mp hd))
  unfold hAlpha
  linarith

/-- Full affirmative answer to JSP-000912 / Erdős 1099, for every real α > 1.
    The witness n is strictly positive and exceeds any prescribed cutoff. -/
theorem jsp_000912_full :
    ∀ α : ℝ, 1 < α → ∃ C : ℝ, 0 < C ∧
      ∀ M : ℕ, ∃ n : ℕ, 0 < n ∧ M ≤ n ∧ hAlpha α n ≤ C := by
  intro α hα
  have hβ : 0 < α - 1 := by linarith
  obtain ⟨r, hr⟩ := exists_nat_ge (4 / (α - 1))
  have hrprod : 4 ≤ (r : ℝ) * (α - 1) := (div_le_iff₀ hβ).mp hr
  have hrpos : 0 < (r : ℝ) := by nlinarith
  have hr1 : 1 ≤ r := by exact_mod_cast hrpos
  have hB : (0 : ℝ) < scaleConstant r := by
    unfold scaleConstant
    positivity
  refine ⟨64 * (scaleConstant r : ℝ) ^ 2, by positivity, ?_⟩
  intro M
  exact ⟨candidate r M, candidate_pos r M, index_le_candidate r M hr1,
    hAlpha_candidate_bound α r M hα hrprod⟩

/-- Exact conventional quantifier form, without additional witness conditions. -/
theorem erdos_1099 :
    ∀ α : ℝ, 1 < α → ∃ C : ℝ, ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ hAlpha α n ≤ C := by
  intro α hα
  obtain ⟨C, _, hC⟩ := jsp_000912_full α hα
  refine ⟨C, ?_⟩
  intro M
  obtain ⟨n, _, hn, hbound⟩ := hC M
  exact ⟨n, hn, hbound⟩

end JSP912
