import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-! # Prime denominator obstructions for JSP-000250

Formalization of the upper-bound method in Liu and Sawhney (2024),
Theorem 1.6, Section 4. Mathematical attribution stays with the cited authors
and Erdős and Graham. This module does not prove the matching lower bound.
-/

open Finset
open scoped BigOperators

namespace JSP000250

/-- A distinct-unit-fraction representation of one, with least denominator t. -/
def Representable (N t : ℕ) : Prop :=
  0 < t ∧ ∃ S : Finset ℕ, t ∈ S ∧
    (∀ n ∈ S, t ≤ n ∧ n ≤ N) ∧ ∑ n ∈ S, (1 : ℚ) / n = 1

lemma clear_denominators (S : Finset ℕ) (D : ℕ)
    (hpos : ∀ n ∈ S, 0 < n) (hdvd : ∀ n ∈ S, n ∣ D) :
    (D : ℚ) * (∑ n ∈ S, (1 : ℚ) / n) = (∑ n ∈ S, D / n : ℕ) := by
  rw [mul_sum, Nat.cast_sum]
  apply sum_congr rfl
  intro n hn
  rw [Nat.cast_div (K := ℚ) (hdvd n hn) (by exact_mod_cast Nat.ne_of_gt (hpos n hn))]
  ring

lemma prime_obstruction_split (p m : ℕ) (hp : p.Prime)
    (U V : Finset ℕ) (hU : U ⊆ Icc 1 m) (h1 : 1 ∈ U)
    (hVpos : ∀ n ∈ V, 0 < n) (hVprime : ∀ n ∈ V, ¬ p ∣ n)
    (hbound : m * Nat.lcmUpto m < p) :
    (∑ k ∈ U, (1 : ℚ) / k) / p + (∑ n ∈ V, (1 : ℚ) / n) ≠ 1 := by
  let L := Nat.lcmUpto m
  let A := ∑ k ∈ U, L / k
  let B := ∏ n ∈ V, n
  let C := ∑ n ∈ V, B / n
  have hL : 0 < L := Nat.lcmUpto_pos m
  have hLU : ∀ k ∈ U, k ∣ L := by
    intro k hk
    exact Finset.dvd_lcm (f := id) (hU hk)
  have hUpos : ∀ k ∈ U, 0 < k := fun k hk => (mem_Icc.mp (hU hk)).1
  have hApos : 0 < A := by
    have hle : L / 1 ≤ A := single_le_sum (fun _ _ => Nat.zero_le _) h1
    simpa using lt_of_lt_of_le hL (by simpa using hle)
  have hAupper : A ≤ m * L := by
    calc
      A ≤ ∑ _k ∈ U, L := sum_le_sum (fun k _ => Nat.div_le_self L k)
      _ = U.card * L := by simp
      _ ≤ m * L := Nat.mul_le_mul_right L (by
        have hc := card_le_card hU
        simpa using hc)
  have hAlt : A < p := lt_of_le_of_lt hAupper hbound
  have hBnot : ¬ p ∣ B := by
    intro h
    obtain ⟨n, hn, hpn⟩ := (hp.prime.dvd_finsetProd_iff (fun n : ℕ => n)).mp h
    exact hVprime n hn hpn
  have hq := clear_denominators U L hUpos hLU
  have hr := clear_denominators V B hVpos (fun n hn => dvd_prod_of_mem (fun n => n) hn)
  change (L : ℚ) * _ = (A : ℚ) at hq
  change (B : ℚ) * _ = (C : ℚ) at hr
  intro h
  have hmul : (p * L * B : ℚ) = (B * A + p * L * C : ℕ) := by
    push_cast
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    calc
      (p : ℚ) * L * B = (p : ℚ) * L * B *
          ((∑ k ∈ U, (1 : ℚ) / k) / p + ∑ n ∈ V, (1 : ℚ) / n) := by rw [h]; ring
      _ = (B : ℚ) * ((L : ℚ) * ∑ k ∈ U, (1 : ℚ) / k) +
          (p : ℚ) * L * ((B : ℚ) * ∑ n ∈ V, (1 : ℚ) / n) := by field_simp
      _ = (B : ℚ) * A + (p : ℚ) * L * C := by rw [hq, hr]
  have hnat : p * L * B = B * A + p * L * C := by exact_mod_cast hmul
  have hBA : p ∣ B * A := by
    have hd : p ∣ B * A + p * L * C := hnat ▸ dvd_mul_of_dvd_left (dvd_mul_right p L) B
    exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left (dvd_mul_right p L) C)).mpr hd
  have hpa : p ∣ A := (hp.dvd_mul.mp hBA).resolve_left hBnot
  exact (not_lt_of_ge (Nat.le_of_dvd hApos hpa)) hAlt

/-- The explicit obstruction; valid for all finite denominator bounds. -/
theorem prime_not_representable (N p m : ℕ) (hp : p.Prime)
    (hN : N ≤ p * m) (hbound : m * Nat.lcmUpto m < p) :
    ¬ Representable N p := by
  rintro ⟨hp0, S, hpS, hS, hsum⟩
  let T := S.filter (fun n => p ∣ n)
  let V := S.filter (fun n => ¬ p ∣ n)
  let U := T.image (fun n => n / p)
  have hT : ∀ n ∈ T, n ∈ S ∧ p ∣ n := by simp [T]
  have hinj : Set.InjOn (fun n : ℕ => n / p) ↑T := by
    intro a ha b hb hab
    change a / p = b / p at hab
    have ha' := Nat.div_mul_cancel (hT a ha).2
    have hb' := Nat.div_mul_cancel (hT b hb).2
    calc
      a = (a / p) * p := ha'.symm
      _ = (b / p) * p := by rw [hab]
      _ = b := hb'
  have hU : U ⊆ Icc 1 m := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnS := hS n (hT n hn).1
    apply mem_Icc.mpr
    constructor
    · exact Nat.one_le_div_iff hp0 |>.mpr hnS.1
    · exact Nat.div_le_of_le_mul (by nlinarith [hnS.2])
  have h1 : 1 ∈ U := by
    have : p ∈ T := by simp [T, hpS]
    change 1 ∈ T.image (fun n => n / p)
    exact mem_image.mpr ⟨p, this, Nat.div_self hp0⟩
  have hVpos : ∀ n ∈ V, 0 < n := by
    intro n hn
    exact lt_of_lt_of_le hp0 (hS n (mem_filter.mp hn).1).1
  have hVp : ∀ n ∈ V, ¬ p ∣ n := fun _ hn => (mem_filter.mp hn).2
  apply prime_obstruction_split p m hp U V hU h1 hVpos hVp hbound
  have hUeq : (∑ k ∈ U, (1 : ℚ) / k) / p = ∑ n ∈ T, (1 : ℚ) / n := by
    rw [show U = T.image (fun n => n / p) from rfl, sum_image hinj, sum_div]
    apply sum_congr rfl
    intro n hn
    rw [div_div, ← Nat.cast_mul, Nat.div_mul_cancel (hT n hn).2]
  rw [hUeq]
  simpa [T, V, sum_filter_add_sum_filter_not] using hsum

lemma exists_exception (N : ℕ) : ∃ t, 0 < t ∧ ¬ Representable N t := by
  refine ⟨N + 1, by omega, ?_⟩
  rintro ⟨_, S, ht, hS, _⟩
  have := (hS (N + 1) ht).2
  omega

/-- The least positive integer which cannot be a least denominator. -/
noncomputable def firstException (N : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_exception N)

theorem firstException_spec (N : ℕ) :
    0 < firstException N ∧ ¬ Representable N (firstException N) := by
  classical
  exact Nat.find_spec (exists_exception N)

theorem firstException_le {N t : ℕ} (ht : 0 < t) (h : ¬ Representable N t) :
    firstException N ≤ t := by
  classical
  exact Nat.find_min' (exists_exception N) ⟨ht, h⟩

lemma log_lcm_bound (m : ℕ) (hm : 0 < m) :
    Real.log ((m * Nat.lcmUpto m : ℕ) : ℝ) ≤ 8 * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hLR : (0 : ℝ) < Nat.lcmUpto m := by exact_mod_cast Nat.lcmUpto_pos m
  have hpsi := Chebyshev.psi_le_const_mul_self (x := (m : ℝ)) (by positivity)
  rw [Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have hfour : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    norm_num at this ⊢
    exact this
  rw [Nat.cast_mul, Real.log_mul hmR.ne' hLR.ne']
  have hlogm := Real.log_le_self hmR.le
  nlinarith

/-- A full quantified upper bound: the constant 128 is not optimized. -/
theorem prime_exception_upper_bound (N : ℕ) (hN : 0 < N)
    (hlog : 128 ≤ Real.log (N : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ ¬ Representable N p ∧
      (p : ℝ) ≤ 128 * N / Real.log (N : ℝ) := by
  let R : ℝ := N
  let z := Real.log R
  have hR : 0 < R := by dsimp [R]; exact_mod_cast hN
  have hz128 : 128 ≤ z := hlog
  have hz : 0 < z := by linarith
  have hzR : z ≤ R := Real.log_le_self hR.le
  let x := 64 * R / z
  have hx64 : 64 ≤ x := by
    apply (le_div_iff₀ hz).mpr
    nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hfloor : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hf := Nat.lt_floor_add_one x
  have hf' := Nat.floor_le hx0
  have hpgtR : (⌊x⌋₊ : ℝ) < p := by exact_mod_cast hpgt
  have hpleR : (p : ℝ) ≤ 2 * (⌊x⌋₊ : ℝ) := by exact_mod_cast hple
  have hpx : x / 2 < (p : ℝ) := by linarith
  have hpz : 32 * R < (p : ℝ) * z := by
    have hxp : x < 2 * (p : ℝ) := by linarith
    have := (div_lt_iff₀ hz).mp hxp
    nlinarith
  have hpupper : (p : ℝ) ≤ 128 * R / z := by
    have h : (p : ℝ) ≤ 2 * x := by linarith
    calc
      (p : ℝ) ≤ 2 * x := h
      _ = 128 * R / z := by dsimp [x]; ring
  have hpN : p ≤ N := by
    have hle : (p : ℝ) ≤ R := hpupper.trans ((div_le_iff₀ hz).mpr (by nlinarith))
    dsimp [R] at hle
    exact_mod_cast hle
  let m : ℕ := N / p + 1
  have hm : 0 < m := Nat.succ_pos _
  have hNm : N ≤ p * m := by
    have hrem := Nat.mod_lt N hp.pos
    have hdiv := Nat.div_add_mod N p
    dsimp [m]
    nlinarith
  have hmR : (m : ℝ) ≤ z / 32 + 1 := by
    have hd : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have hr : R / p < z / 32 := (div_lt_iff₀ hpR).mpr (by nlinarith)
    dsimp [m]
    push_cast
    change ((N / p : ℕ) : ℝ) + 1 ≤ z / 32 + 1
    dsimp [R] at hr
    linarith
  have hzsqrt : z ≤ 2 * Real.sqrt R := by
    have hh := Real.log_le_rpow_div (ε := (1 / 2 : ℝ)) hR.le (by norm_num)
    rw [← Real.sqrt_eq_rpow] at hh
    calc
      z ≤ Real.sqrt R / (1 / 2) := hh
      _ = 2 * Real.sqrt R := by ring
  have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsquare := Real.sq_sqrt hR.le
  have hsqrtp : Real.sqrt R < p := by
    by_contra hh
    have hps : (p : ℝ) ≤ Real.sqrt R := le_of_not_gt hh
    have hprod := mul_le_mul hps hzsqrt hz.le (le_of_lt hsqrt)
    nlinarith
  have hlogp : z / 2 < Real.log (p : ℝ) := by
    have hh := Real.log_lt_log hsqrt hsqrtp
    rwa [Real.log_sqrt hR.le] at hh
  have hlogML := log_lcm_bound m hm
  have hML : m * Nat.lcmUpto m < p := by
    have hposML : (0 : ℝ) < (m * Nat.lcmUpto m : ℕ) := by
      exact_mod_cast Nat.mul_pos hm (Nat.lcmUpto_pos m)
    have hlt : Real.log ((m * Nat.lcmUpto m : ℕ) : ℝ) < Real.log (p : ℝ) := by
      nlinarith
    exact_mod_cast (Real.log_lt_log_iff hposML hpR).mp hlt
  exact ⟨p, hp, hpN, prime_not_representable N p m hp hNm hML, hpupper⟩

theorem smaller_denominators_representable (N t : ℕ)
    (ht : 0 < t) (hlt : t < firstException N) : Representable N t := by
  by_contra h
  exact (not_le_of_gt hlt) (firstException_le ht h)

theorem firstException_upper_bound (N : ℕ) (hN : 0 < N)
    (hlog : 128 ≤ Real.log (N : ℝ)) :
    (firstException N : ℝ) ≤ 128 * N / Real.log (N : ℝ) := by
  obtain ⟨p, hp, _, hrep, hb⟩ := prime_exception_upper_bound N hN hlog
  have hle := firstException_le hp.pos hrep
  exact le_trans (by exact_mod_cast hle) hb

/-- The upper-bound half of Liu--Sawhney Theorem 1.6. -/
theorem firstException_isBigO :
    (fun N : ℕ => (firstException N : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨128, ?_⟩
  have hlog : ∀ᶠ N : ℕ in Filter.atTop, 128 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 128)
  filter_upwards [hlog, Filter.eventually_ge_atTop (1 : ℕ)] with N hl hn
  have hN : 0 < N := by omega
  have h := firstException_upper_bound N hN hl
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ firstException N from Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg _) hlogpos.le)]
  simpa only [mul_div_assoc] using h

end JSP000250
