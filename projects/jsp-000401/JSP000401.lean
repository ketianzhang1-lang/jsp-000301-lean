/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Prepared for the submitting account ketianzhang1-lang with OpenAI ChatGPT assistance.
Mathematical construction: Paul Turán. See README.md for scope and attribution.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open Finset
open scoped BigOperators

namespace JSP000401

def Good (a b c : Fin 3) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨
  (a = b ∧ c = a + 1) ∨
  (a = c ∧ b = a + 1) ∨
  (b = c ∧ a = b + 1)

instance (a b c : Fin 3) : Decidable (Good a b c) := inferInstanceAs
  (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)))

theorem good_swap : ∀ a b c, Good a b c ↔ Good b a c := by decide
theorem good_cycle : ∀ a b c, Good a b c ↔ Good b c a := by decide

theorem no_four : ∀ a b c d : Fin 3,
    ¬ (Good a b c ∧ Good a b d ∧ Good a c d ∧ Good b c d) := by decide

theorem fifteen : (∑ f : Fin 3 → Fin 3, if Good (f 0) (f 1) (f 2) then 1 else 0) = (15 : ℕ) := by decide


variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every ordering of three distinct vertices has an allowed color pattern. -/
def GoodSet (c : V → Fin 3) (e : Finset V) : Prop :=
  ∀ a ∈ e, ∀ b ∈ e, ∀ d ∈ e,
    a ≠ b → a ≠ d → b ≠ d → Good (c a) (c b) (c d)

instance (c : V → Fin 3) (e : Finset V) : Decidable (GoodSet c e) :=
  inferInstanceAs (Decidable (∀ a ∈ e, ∀ b ∈ e, ∀ d ∈ e,
    a ≠ b → a ≠ d → b ≠ d → Good (c a) (c b) (c d)))

def edges (c : V → Fin 3) : Finset (Finset V) :=
  (Finset.univ.powersetCard 3).filter (GoodSet c)

theorem uniform (c : V → Fin 3) {e : Finset V} (he : e ∈ edges c) : e.card = 3 :=
  (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

theorem good_permutation : ∀ (f : Fin 3 → Fin 3) (i j k : Fin 3),
    i ≠ j → i ≠ k → j ≠ k →
    (Good (f 0) (f 1) (f 2) ↔ Good (f i) (f j) (f k)) := by decide

noncomputable def enumeration (e : Finset V) (he : e.card = 3) : Fin 3 ≃ e :=
  (Fintype.equivFinOfCardEq (by simpa using he)).symm

omit [Fintype V] [DecidableEq V] in
theorem goodSet_iff (c : V → Fin 3) (e : Finset V) (he : e.card = 3) :
    GoodSet c e ↔ Good (c (enumeration e he 0)) (c (enumeration e he 1))
      (c (enumeration e he 2)) := by
  let q := enumeration e he
  constructor
  · intro h
    apply h _ (q 0).property _ (q 1).property _ (q 2).property
    all_goals
      intro eq
      have := q.injective (Subtype.ext eq)
      norm_num at this
  · intro h a ha b hb d hd hab had hbd
    let i := q.symm ⟨a, ha⟩
    let j := q.symm ⟨b, hb⟩
    let k := q.symm ⟨d, hd⟩
    have hij : i ≠ j := fun h => hab (congrArg Subtype.val (q.symm.injective h))
    have hik : i ≠ k := fun h => had (congrArg Subtype.val (q.symm.injective h))
    have hjk : j ≠ k := fun h => hbd (congrArg Subtype.val (q.symm.injective h))
    have hp := (good_permutation (fun x => c (q x)) i j k hij hik hjk).mp h
    simpa [i, j, k] using hp

theorem tetrahedron_free (c : V → Fin 3) (a b d f : V)
    (hab : a ≠ b) (had : a ≠ d) (haf : a ≠ f)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f) :
    ¬ ({a,b,d} ∈ edges c ∧ {a,b,f} ∈ edges c ∧
      {a,d,f} ∈ edges c ∧ {b,d,f} ∈ edges c) := by
  rintro ⟨h₁,h₂,h₃,h₄⟩
  apply no_four (c a) (c b) (c d) (c f)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mem_filter.mp h₁).2 a (by simp) b (by simp) d (by simp) hab had hbd
  · exact (mem_filter.mp h₂).2 a (by simp) b (by simp) f (by simp) hab haf hbf
  · exact (mem_filter.mp h₃).2 a (by simp) d (by simp) f (by simp) had haf hdf
  · exact (mem_filter.mp h₄).2 b (by simp) d (by simp) f (by simp) hbd hbf hdf

omit [Fintype V] in
theorem sum_on_three (e : Finset V) (he : e.card = 3) :
    (∑ c : e → Fin 3, if Good (c (enumeration e he 0)) (c (enumeration e he 1))
      (c (enumeration e he 2)) then 1 else 0) = (15 : ℕ) := by
  let q := Equiv.piCongrLeft (fun _ : e => Fin 3) (enumeration e he)
  calc
    _ = ∑ c : Fin 3 → Fin 3, if Good (c 0) (c 1) (c 2) then 1 else 0 := by
      symm
      apply Fintype.sum_equiv q
      intro c
      simp [q]
    _ = 15 := fifteen

theorem edge_frequency (e : Finset V) (he : e.card = 3) :
    (∑ c : V → Fin 3, if GoodSet c e then 1 else 0) =
      15 * 3 ^ (Fintype.card V - 3) := by
  classical
  let q := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ e) (fun _ => Fin 3)
  calc
    _ = ∑ c : (e → Fin 3) × ({v : V // v ∉ e} → Fin 3),
        if Good (c.1 (enumeration e he 0)) (c.1 (enumeration e he 1))
          (c.1 (enumeration e he 2)) then 1 else 0 := by
      apply Fintype.sum_equiv q
      intro c
      simp only [goodSet_iff c e he]
      rfl
    _ = 15 * 3 ^ (Fintype.card V - 3) := by
      rw [Fintype.sum_prod_type]
      have hinner (x : e → Fin 3) :
          (∑ _y : {v : V // v ∉ e} → Fin 3,
            if Good (x (enumeration e he 0)) (x (enumeration e he 1))
              (x (enumeration e he 2)) then 1 else 0) =
          Fintype.card ({v : V // v ∉ e} → Fin 3) *
            (if Good (x (enumeration e he 0)) (x (enumeration e he 1))
              (x (enumeration e he 2)) then 1 else 0) := by
        exact Finset.sum_const _
      simp_rw [hinner]
      rw [← Finset.mul_sum]
      rw [sum_on_three e he, Nat.mul_comm]
      congr 1
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl]
      simp [he]


theorem total_edges :
    (∑ c : V → Fin 3, (edges c).card) =
      (Fintype.card V).choose 3 * (15 * 3 ^ (Fintype.card V - 3)) := by
  classical
  unfold edges
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ (Finset.univ : Finset V).powersetCard 3,
        15 * 3 ^ (Fintype.card V - 3) := by
      apply Finset.sum_congr rfl
      intro e he
      exact edge_frequency e (Finset.mem_powersetCard.mp he).2
    _ = _ := by simp

theorem exists_dense_coloring (n : ℕ) :
    ∃ c : Fin n → Fin 3, 5 * n.choose 3 ≤ 9 * (edges c).card := by
  classical
  by_cases hn : 3 ≤ n
  · have hpow : 3 ^ n = 27 * 3 ^ (n - 3) := by
      conv_lhs => rw [show n = 3 + (n - 3) by omega, pow_add]
      norm_num
    have hsum : (∑ _c : Fin n → Fin 3, 5 * n.choose 3) =
        ∑ c : Fin n → Fin 3, 9 * (edges c).card := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ← Finset.mul_sum, total_edges]
      simp only [Fintype.card_fin]
      rw [hpow]
      simp only [Nat.cast_id]
      ring
    obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin n → Fin 3)).Nonempty) hsum.le
    exact ⟨c, hc⟩
  · refine ⟨fun _ => 0, ?_⟩
    rw [Nat.choose_eq_zero_of_lt (by omega : n < 3)]
    omega

/-- A finite simple three-uniform hypergraph with no tetrahedron. -/
def Valid (E : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 3) ∧
  (∀ a b d f : V, a ≠ b → a ≠ d → a ≠ f → b ≠ d → b ≠ f → d ≠ f →
    ¬ ({a,b,d} ∈ E ∧ {a,b,f} ∈ E ∧ {a,d,f} ∈ E ∧ {b,d,f} ∈ E))

/-- Turán's classical 5/9 lower bound, for every finite order, with integer rounding. -/
theorem turan_lower_bound (n : ℕ) :
    ∃ E : Finset (Finset (Fin n)), Valid E ∧ 5 * n.choose 3 ≤ 9 * E.card := by
  obtain ⟨c, hc⟩ := exists_dense_coloring n
  exact ⟨edges c, ⟨fun _ he => uniform c he, tetrahedron_free c⟩, hc⟩

end JSP000401
