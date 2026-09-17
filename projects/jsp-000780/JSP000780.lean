/-
Copyright (c) 2026 JSP-000780 contributors. Released under the MIT license.
Prepared with OpenAI ChatGPT assistance under the submitting account's direction.
The r=6 binomial construction is a specialization of the construction attributed
by Formal Conjectures to GPT-5.5 Pro prompted by Liam Price. See PROVENANCE.md.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.GCDMonoid.Finset

set_option maxRecDepth 4096

namespace JSP000780

/-- Every prime divisor occurs to exponent at least six. -/
def SixFull (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 6 ∣ n

lemma sixFull_pow (a k : ℕ) (hk : 6 ≤ k) : SixFull (a ^ k) := by
  intro p hp hd
  exact (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 6).trans (Nat.pow_dvd_pow a hk)

lemma SixFull.mul {a b : ℕ} (ha : SixFull a) (hb : SixFull b) : SixFull (a * b) := by
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (ha p hp h) b
  · exact dvd_mul_of_dvd_right (hb p hp h) a

lemma sixFull_c1 : SixFull (12 * 30 ^ 6) := by
  have h : 12 * 30 ^ 6 = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 := by norm_num
  rw [h]
  exact ((sixFull_pow 2 8 (by omega)).mul (sixFull_pow 3 7 (by omega))).mul
    (sixFull_pow 5 6 (by omega))

lemma sixFull_c2 : SixFull (40 * 30 ^ 18) := by
  have h : 40 * 30 ^ 18 = 2 ^ 21 * 3 ^ 18 * 5 ^ 19 := by norm_num
  rw [h]
  exact ((sixFull_pow 2 21 (by omega)).mul (sixFull_pow 3 18 (by omega))).mul
    (sixFull_pow 5 19 (by omega))

lemma sixFull_c3 : SixFull (12 * 30 ^ 30) := by
  have h : 12 * 30 ^ 30 = 2 ^ 32 * 3 ^ 31 * 5 ^ 30 := by norm_num
  rw [h]
  exact ((sixFull_pow 2 32 (by omega)).mul (sixFull_pow 3 31 (by omega))).mul
    (sixFull_pow 5 30 (by omega))

lemma identity (x y : ℕ) (h : y ≤ x) :
    (x-y)^6 + 12*x^5*y + 40*x^3*y^3 + 12*x*y^5 = (x+y)^6 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  ring

lemma term_order (x y : ℕ) (hy : 0 < y) (hxy : 1000*y < x) :
    12*x*y^5 < 40*x^3*y^3 ∧
    40*x^3*y^3 < 12*x^5*y ∧
    12*x^5*y < (x-y)^6 := by
  have hx : 0 < x := by omega
  have hyx : y < x := by omega
  have hyx2 : 2*y < x := by omega
  have hy2 : 0 < y^2 := by positivity
  have hsq : y^2 < x^2 := Nat.pow_lt_pow_left hyx (by decide)
  have hsq2 : (2*y)^2 < x^2 := Nat.pow_lt_pow_left hyx2 (by decide)
  constructor
  · calc
      12*x*y^5 = (12*y^2)*(x*y^3) := by ring
      _ < (40*x^2)*(x*y^3) := Nat.mul_lt_mul_of_pos_right (by nlinarith) (by positivity)
      _ = 40*x^3*y^3 := by ring
  constructor
  · calc
      40*x^3*y^3 = (40*y^2)*(x^3*y) := by ring
      _ < (12*x^2)*(x^3*y) := Nat.mul_lt_mul_of_pos_right (by nlinarith) (by positivity)
      _ = 12*x^5*y := by ring
  · have hsmall : 64*(12*x^5*y) < x^6 := by
      calc
        64*(12*x^5*y) = (768*y)*x^5 := by ring
        _ < x*x^5 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = x^6 := by ring
    have hlarge : x^6 ≤ 64*(x-y)^6 := by
      calc
        x^6 ≤ (2*(x-y))^6 := Nat.pow_le_pow_left (by omega) 6
        _ = 64*(x-y)^6 := by ring
    omega

/-- A parameter coprime to 30, chosen large enough to separate the four summands. -/
def base (t : ℕ) : ℕ := 30*(t+11)+1

def terms (t : ℕ) : Finset ℕ :=
  let x := (base t)^6
  let y := 30^6
  {(x-y)^6, 12*x^5*y, 40*x^3*y^3, 12*x*y^5}

def total (t : ℕ) : ℕ := ((base t)^6 + 30^6)^6

lemma base_coprime (t : ℕ) : (base t).Coprime 30 := by
  unfold base
  rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left 30

lemma base_large (t : ℕ) : 1000*30^6 < (base t)^6 := by
  have h : 331 ≤ base t := by unfold base; omega
  have hh := Nat.pow_le_pow_left h 6
  norm_num at hh ⊢
  omega

lemma terms_order (t : ℕ) :
    12*(base t)^6*(30^6)^5 < 40*((base t)^6)^3*(30^6)^3 ∧
    40*((base t)^6)^3*(30^6)^3 < 12*((base t)^6)^5*30^6 ∧
    12*((base t)^6)^5*30^6 < ((base t)^6-30^6)^6 :=
  term_order _ _ (by norm_num) (base_large t)

lemma terms_card (t : ℕ) : (terms t).card = 4 := by
  have h := terms_order t
  unfold terms
  simp (disch := simp only [Finset.mem_insert, Finset.mem_singleton]; omega) only
    [Finset.card_insert_of_notMem, Finset.card_singleton]

lemma terms_sum (t : ℕ) : ∑ n ∈ terms t, n = total t := by
  have h := terms_order t
  have hxy : 30^6 ≤ (base t)^6 := by have := base_large t; omega
  unfold terms total
  simp (disch := simp only [Finset.mem_insert, Finset.mem_singleton]; omega) only
    [Finset.sum_insert, Finset.sum_singleton]
  convert identity ((base t)^6) (30^6) hxy using 1; omega

lemma terms_positive (t n : ℕ) (hn : n ∈ terms t) : 0 < n := by
  have hx : 0 < base t := by unfold base; omega
  have hxy : 30^6 < (base t)^6 := by have := base_large t; omega
  unfold terms at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  have hy : 0 < 30^6 := Nat.pow_pos (by decide)
  have hx6 : 0 < (base t)^6 := Nat.pow_pos hx
  rcases hn with h | h | h | h <;> rw [h]
  · exact Nat.pow_pos (Nat.sub_pos_of_lt hxy)
  · exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos hx6)) hy
  · exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos hx6)) (Nat.pow_pos hy)
  · exact Nat.mul_pos (Nat.mul_pos (by decide) hx6) (Nat.pow_pos hy)

lemma terms_sixFull (t n : ℕ) (hn : n ∈ terms t) : SixFull n := by
  unfold terms at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h <;> rw [h]
  · exact sixFull_pow _ 6 (by omega)
  · convert sixFull_c1.mul (sixFull_pow (base t) 30 (by omega)) using 1; ring
  · convert sixFull_c2.mul (sixFull_pow (base t) 18 (by omega)) using 1; ring
  · convert sixFull_c3.mul (sixFull_pow (base t) 6 (by omega)) using 1; ring

lemma total_sixFull (t : ℕ) : SixFull (total t) := sixFull_pow _ 6 (by omega)

lemma first_second_coprime (t : ℕ) :
    (((base t)^6-30^6)^6).Coprime (12*((base t)^6)^5*30^6) := by
  have hle : 30^6 ≤ (base t)^6 := by have := base_large t; omega
  have hc : ((base t)^6).Coprime (30^6) := (base_coprime t).pow 6 6
  have hy : ((base t)^6-30^6).Coprime (30^6) :=
    (Nat.coprime_sub_self_left hle).mpr hc
  have hx : ((base t)^6-30^6).Coprime ((base t)^6) :=
    (Nat.coprime_self_sub_left hle).mpr hc.symm
  have h12 : ((base t)^6-30^6).Coprime 12 := hy.of_dvd_right (by norm_num)
  exact ((h12.mul_right (hx.pow_right 5)).mul_right hy).pow_left 6

lemma gcd_four_eq_one (a b c d : ℕ) (hc : a.Coprime b) :
    ({a,b,c,d} : Finset ℕ).gcd id = 1 := by
  apply Nat.dvd_one.mp
  rw [← hc.gcd_eq_one]
  exact Nat.dvd_gcd
    (Finset.gcd_dvd (Finset.mem_insert_self a _))
    (Finset.gcd_dvd (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)))

lemma terms_gcd (t : ℕ) : (terms t).gcd id = 1 :=
  gcd_four_eq_one _ _ _ _ (first_second_coprime t)

lemma total_strictMono : StrictMono total := by
  intro s t hst
  apply Nat.pow_lt_pow_left _ (by decide)
  apply Nat.add_lt_add_right
  apply Nat.pow_lt_pow_left _ (by decide)
  unfold base
  omega

lemma terms_injective : Function.Injective terms := by
  intro s t h
  apply total_strictMono.injective
  have hh := congrArg (fun S : Finset ℕ => ∑ n ∈ S, n) h
  simpa only [terms_sum] using hh

/-- The r=6 case of the finite-set formulation of Erdős 939.
Coprimality is collective (gcd = 1), not pairwise. -/
def Solution (S : Finset ℕ) : Prop :=
  S.card = 4 ∧ S.gcd id = 1 ∧ SixFull (∑ n ∈ S, n) ∧
    ∀ n ∈ S, 0 < n ∧ SixFull n

/-- Every natural parameter gives four distinct positive six-full numbers,
with collective gcd 1, whose sum is itself six-full. -/
theorem solution_for_every_parameter (t : ℕ) : Solution (terms t) := by
  refine ⟨terms_card t, terms_gcd t, ?_, ?_⟩
  · rw [terms_sum]
    exact total_sixFull t
  · intro n hn
    exact ⟨terms_positive t n hn, terms_sixFull t n hn⟩

/-- There are infinitely many distinct primitive four-term six-full sums. -/
theorem infinitely_many_solutions : Set.Infinite {S : Finset ℕ | Solution S} := by
  apply (Set.infinite_range_of_injective terms_injective).mono
  rintro S ⟨t, rfl⟩
  exact solution_for_every_parameter t

/-- The sums themselves, not only the representing sets, take infinitely many values. -/
theorem infinitely_many_totals : (Set.range total).Infinite :=
  Set.infinite_range_of_injective total_strictMono.injective

/-- The prime-factor-list definition used in the Formal Conjectures statement. -/
def FactorFull (r n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^r ∣ n

lemma sixFull_iff_factorFull (n : ℕ) : SixFull n ↔ FactorFull 6 n := by
  constructor
  · intro h p hp
    have hmem := Nat.mem_primeFactors.mp hp
    exact h p hmem.1 hmem.2.1
  · intro h p hp hd
    by_cases hn : n = 0
    · simp only [hn, dvd_zero]
    · exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)

/-- The finite-set solution predicate from Erdős 939, with names localized here.
`S.gcd id = 1` is the definition of its collective `Finset.Coprime` predicate. -/
def OriginalSolutions (r : ℕ) : Set (Finset ℕ) :=
  {S | S.card = r-2 ∧ S.gcd id = 1 ∧ FactorFull r (∑ n ∈ S, n) ∧
    ∀ n ∈ S, 0 < n ∧ FactorFull r n}

lemma original_six_iff (S : Finset ℕ) : S ∈ OriginalSolutions 6 ↔ Solution S := by
  simp only [OriginalSolutions, Set.mem_ofPred_eq, Solution, show 6-2=4 from rfl,
    ← sixFull_iff_factorFull]

/-- The r=6 case holds with the original finite-set and prime-factor definitions. -/
theorem original_six_infinite : (OriginalSolutions 6).Infinite := by
  have he : OriginalSolutions 6 = {S | Solution S} := by
    ext S
    exact original_six_iff S
  rw [he]
  exact infinitely_many_solutions

/-- A complete negative answer to the universal finiteness variant.
This does not cover r=4 or r=5, or prove the complete all-r≥6 family. -/
theorem not_finite_for_every_r : ¬ ∀ r ≥ 4, (OriginalSolutions r).Finite := by
  intro h
  exact original_six_infinite (h 6 (by omega))

end JSP000780
