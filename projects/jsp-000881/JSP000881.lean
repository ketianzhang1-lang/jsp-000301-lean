/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Prepared with OpenAI ChatGPT assistance.
SReal follows the counting convention of The Formal Conjectures Authors (2026),
FormalConjectures/ErdosProblems/1061.lean, licensed under Apache 2.0.
All proofs below are newly written for this package.

JSP-000881 / Erdos 1061: explicit solution families and a linear lower bound.
This does not prove the conjectured asymptotic S(x) ~ c*x.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

open Finset
open scoped ArithmeticFunction.sigma

namespace JSP000881

/-- Ordered positive solutions with sum at most N. -/
def solutions (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p =>
    p.1 + p.2 ≤ N ∧ σ 1 p.1 + σ 1 p.2 = σ 1 (p.1 + p.2)

def S (N : ℕ) : ℕ := (solutions N).card

/-- Multiplicativity transports any seed when t is coprime to all three entries. -/
theorem scale_solution {a b t : ℕ}
    (h : σ 1 a + σ 1 b = σ 1 (a + b))
    (ha : Nat.Coprime a t) (hb : Nat.Coprime b t)
    (hab : Nat.Coprime (a + b) t) :
    σ 1 (a*t) + σ 1 (b*t) = σ 1 (a*t+b*t) := by
  rw [← add_mul, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ha,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hb,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab,
    ← add_mul, h]

theorem seed_one_two (t : ℕ) (h : Nat.Coprime 6 t) :
    σ 1 t + σ 1 (2*t) = σ 1 (t+2*t) := by
  have h2 : Nat.Coprime 2 t := h.of_dvd_left (by norm_num)
  have h3 : Nat.Coprime 3 t := h.of_dvd_left (by norm_num)
  simpa using scale_solution (a:=1) (b:=2) (t:=t)
    (by decide)
    (Nat.coprime_one_left t) h2 h3

theorem seed_four_five (t : ℕ) (h : Nat.Coprime 30 t) :
    σ 1 (4*t) + σ 1 (5*t) = σ 1 (4*t+5*t) := by
  have h2 : Nat.Coprime 2 t := h.of_dvd_left (by norm_num)
  have h3 : Nat.Coprime 3 t := h.of_dvd_left (by norm_num)
  have h5 : Nat.Coprime 5 t := h.of_dvd_left (by norm_num)
  have h4 : Nat.Coprime 4 t := by simpa using h2.mul_left h2
  have h9 : Nat.Coprime 9 t := by simpa using h3.mul_left h3
  exact scale_solution (by decide) h4 h5 h9

def residueA (i : Fin 30) : ℕ := 3*i.val+1+i.val%2

def residueB (i : Fin 8) : ℕ := ![1,7,11,13,17,19,23,29] i

lemma residueA_bounds (i : Fin 30) : 0 < residueA i ∧ residueA i < 90 := by
  dsimp [residueA]; omega

lemma residueB_bounds : ∀ i, 0 < residueB i ∧ residueB i < 30 := by decide

lemma residueA_coprime : ∀ i, Nat.Coprime (residueA i) 6 := by decide
lemma residueB_coprime : ∀ i, Nat.Coprime (residueB i) 30 := by decide

lemma residueA_injective : Function.Injective residueA := by
  intro i j h; apply Fin.ext; dsimp [residueA] at h; omega
lemma residueB_injective : Function.Injective residueB := by decide

def paramA (k : ℕ) (i : Fin 30) : ℕ := 90*k+residueA i
def paramB (k : ℕ) (i : Fin 8) : ℕ := 30*k+residueB i

lemma paramA_coprime (k : ℕ) (i : Fin 30) : Nat.Coprime 6 (paramA k i) := by
  have h := (Nat.coprime_add_mul_right_left (residueA i) 6 (15*k)).mpr
    (residueA_coprime i)
  convert h.symm using 1
  simp [paramA]
  ring
lemma paramB_coprime (k : ℕ) (i : Fin 8) : Nat.Coprime 30 (paramB k i) := by
  simpa [paramB, Nat.add_comm, Nat.mul_comm] using
    ((Nat.coprime_add_mul_right_left (residueB i) 30 k).mpr (residueB_coprime i)).symm

lemma paramA_injective {k l : ℕ} {i j : Fin 30} (h : paramA k i = paramA l j) :
    k=l ∧ i=j := by
  have hi := residueA_bounds i; have hj := residueA_bounds j
  have hk : k=l := by dsimp [paramA] at h; omega
  refine ⟨hk, residueA_injective ?_⟩
  dsimp [paramA] at h; omega
lemma paramB_injective {k l : ℕ} {i j : Fin 8} (h : paramB k i = paramB l j) :
    k=l ∧ i=j := by
  have hi := residueB_bounds i; have hj := residueB_bounds j
  have hk : k=l := by dsimp [paramB] at h; omega
  refine ⟨hk, residueB_injective ?_⟩
  dsimp [paramB] at h; omega

/-- 30 first-seed parameters and 8 second-seed parameters per block. -/
abbrev Index (q : ℕ) := Fin q × ((Fin 30 ⊕ Fin 8) × Bool)

def witness {q : ℕ} (v : Index q) : ℕ × ℕ :=
  let p := match v.2.1 with
    | Sum.inl i => (paramA v.1.val i, 2*paramA v.1.val i)
    | Sum.inr i => (4*paramB v.1.val i, 5*paramB v.1.val i)
  if v.2.2 then p.swap else p

lemma witness_mem {N : ℕ} (v : Index (N/270)) : witness v ∈ solutions N := by
  rcases v with ⟨k, i, orient⟩
  have hk := k.isLt
  have hdiv : 270*(N/270) ≤ N := Nat.mul_div_le N 270
  cases i with
  | inl i =>
    have hr := residueA_bounds i
    have ht : 0 < paramA k.val i ∧ 3*paramA k.val i ≤ N := by
      dsimp [paramA]; omega
    have hs := seed_one_two (paramA k.val i) (paramA_coprime k.val i)
    cases orient <;> simp only [witness, Bool.false_eq_true, ↓reduceIte, Prod.swap,
      solutions, mem_filter, mem_product, mem_Icc] <;>
      constructor
    all_goals first | omega | constructor; omega; first | exact hs | simpa [Nat.add_comm] using hs
  | inr i =>
    have hr := residueB_bounds i
    have ht : 0 < paramB k.val i ∧ 9*paramB k.val i ≤ N := by
      dsimp [paramB]; omega
    have hs := seed_four_five (paramB k.val i) (paramB_coprime k.val i)
    cases orient <;> simp only [witness, Bool.false_eq_true, ↓reduceIte, Prod.swap,
      solutions, mem_filter, mem_product, mem_Icc] <;>
      constructor
    all_goals first | omega | constructor; omega; first | exact hs | simpa [Nat.add_comm] using hs

lemma witness_injective (q : ℕ) : Function.Injective (@witness q) := by
  rintro ⟨k, i, o⟩ ⟨l, j, p⟩ h
  have apos : ∀ (k : ℕ) (i : Fin 30), 0 < paramA k i := by
    intro k i; have := (residueA_bounds i).1; dsimp [paramA]; omega
  have bpos : ∀ (k : ℕ) (i : Fin 8), 0 < paramB k i := by
    intro k i; have := (residueB_bounds i).1; dsimp [paramB]; omega
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hi := apos k.val i; have hj := apos l.val j
      cases o <;> cases p <;>
        simp only [witness, Bool.false_eq_true, ↓reduceIte, Prod.swap,
          Prod.mk.injEq] at h
      all_goals first
        | obtain ⟨hk, hij⟩ := paramA_injective (show paramA k.val i = paramA l.val j by omega)
          have hkl : k=l := Fin.ext hk
          subst l; subst j; rfl
        | omega
    | inr j =>
      have hi := apos k.val i; have hj := bpos l.val j
      cases o <;> cases p <;>
        simp only [witness, Bool.false_eq_true, ↓reduceIte, Prod.swap,
          Prod.mk.injEq] at h <;> omega
  | inr i =>
    cases j with
    | inl j =>
      have hi := bpos k.val i; have hj := apos l.val j
      cases o <;> cases p <;>
        simp only [witness, Bool.false_eq_true, ↓reduceIte, Prod.swap,
          Prod.mk.injEq] at h <;> omega
    | inr j =>
      have hi := bpos k.val i; have hj := bpos l.val j
      cases o <;> cases p <;>
        simp only [witness, Bool.false_eq_true, ↓reduceIte, Prod.swap,
          Prod.mk.injEq] at h
      all_goals first
        | obtain ⟨hk, hij⟩ := paramB_injective (show paramB k.val i = paramB l.val j by omega)
          have hkl : k=l := Fin.ext hk
          subst l; subst j; rfl
        | omega

/-- At least 76 distinct ordered solutions occur per complete block of length 270. -/
theorem block_lower_bound (N : ℕ) : 76*(N/270) ≤ S N := by
  let f : Index (N/270) → ↥(solutions N) := fun v => ⟨witness v, witness_mem v⟩
  have hf : Function.Injective f := by
    intro u v h
    exact witness_injective _ (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Index, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc

/-- A rational-coefficient bound, expressed without division. -/
theorem linear_lower_bound (N : ℕ) : 38*N ≤ 135*S N + 10222 := by
  have hb := block_lower_bound N
  have hr : N % 270 < 270 := Nat.mod_lt N (by decide)
  have he : N % 270 + 270*(N/270) = N := Nat.mod_add_div N 270
  omega

/-- The real-argument ordered count used in the original problem. -/
noncomputable def SReal (x : ℝ) : ℝ :=
  (((Icc 1 ⌊x⌋₊) ×ˢ (Icc 1 ⌊x⌋₊)).filter fun p : ℕ × ℕ =>
    (p.1 : ℝ) + p.2 ≤ x ∧ σ 1 p.1 + σ 1 p.2 = σ 1 (p.1+p.2)).card

lemma realCount_eq (x : ℝ) (hx : 0 ≤ x) : SReal x = (S ⌊x⌋₊ : ℝ) := by
  unfold SReal S solutions
  congr 2
  apply Finset.filter_congr
  intro p hp
  rw [← Nat.cast_add, ← Nat.le_floor_iff hx]

/-- An explicit linear lower bound for the original real-valued counting function. -/
theorem original_real_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    (38/135 : ℝ)*x - 76 ≤ SReal x := by
  rw [realCount_eq x hx]
  have hb : (38:ℝ)*⌊x⌋₊ ≤ 135*(S ⌊x⌋₊ : ℝ)+10222 := by
    exact_mod_cast linear_lower_bound ⌊x⌋₊
  have hr := Nat.lt_floor_add_one x
  linarith

/-- The lower asymptotic coefficient is at least 38/135; convergence is not asserted. -/
theorem asymptotic_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, 0 < X ∧ ∀ x : ℝ, X ≤ x → (38/135 : ℝ)-ε ≤ SReal x/x := by
  refine ⟨max 1 (76/ε), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hεx : 76 ≤ ε*x := by
    have h := le_trans (le_max_right 1 (76/ε)) hx
    have := (div_le_iff₀ hε).mp h
    nlinarith
  apply (le_div_iff₀ hx0).mpr
  have := original_real_lower_bound x hx0.le
  nlinarith

/-- There are infinitely many ordered positive solutions. -/
theorem infinitely_many_solutions :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧
      σ 1 p.1 + σ 1 p.2 = σ 1 (p.1+p.2)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f:=fun k : ℕ => (6*k+1,2*(6*k+1)))
  · intro k l h
    have := congrArg Prod.fst h
    dsimp at this
    omega
  · intro k
    refine ⟨by omega, by omega, seed_one_two _ ?_⟩
    simpa only [Nat.mul_comm, Nat.add_comm] using
      ((Nat.coprime_add_mul_right_left 1 6 k).mpr (Nat.coprime_one_left 6)).symm

end JSP000881
