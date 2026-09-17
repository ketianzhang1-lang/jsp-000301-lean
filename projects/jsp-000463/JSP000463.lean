import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
Finite-field incidence lower bound for JSP-000463 / Erdos 573.
This is the classical biaffine-plane construction, not a new mathematical result.
The precise asymptotic extremal problem is not resolved here.
-/

namespace JSP000463
open Finset SimpleGraph

abbrev Vertex (K : Type*) := (K × K) ⊕ (K × K)

variable (K : Type*) [Field K]

/-- Left vertices are points `(x,y)`; right vertices are nonvertical lines `(a,b)`. -/
def incidence : SimpleGraph (Vertex K) where
  Adj u v := match u, v with
    | .inl p, .inr l => p.2 = l.1 * p.1 + l.2
    | .inr l, .inl p => p.2 = l.1 * p.1 + l.2
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

instance [DecidableEq K] : DecidableRel (incidence K).Adj := by
  intro u v; cases u <;> cases v <;> dsimp [incidence] <;> infer_instance

variable {K}

/-- Two distinct points are incident to at most one nonvertical line. -/
theorem rectangle (p r l s : K × K)
    (hpl : p.2 = l.1 * p.1 + l.2) (hps : p.2 = s.1 * p.1 + s.2)
    (hrl : r.2 = l.1 * r.1 + l.2) (hrs : r.2 = s.1 * r.1 + s.2) :
    p = r ∨ l = s := by
  have h : (l.1 - s.1) * (p.1 - r.1) = 0 := by
    linear_combination -hpl + hps + hrl - hrs
  rcases mul_eq_zero.mp h with h | h
  · right
    have ha : l.1 = s.1 := sub_eq_zero.mp h
    apply Prod.ext ha
    rw [ha] at hpl
    linear_combination -hpl + hps
  · left
    have hx : p.1 = r.1 := sub_eq_zero.mp h
    apply Prod.ext hx
    rw [hx] at hpl
    linear_combination hpl - hrl

theorem no_triangle (a b c : Vertex K)
    (hab : (incidence K).Adj a b) (hbc : (incidence K).Adj b c) :
    ¬ (incidence K).Adj c a := by
  cases a <;> cases b <;> cases c <;> simp_all [incidence]

theorem no_rectangle (a b c d : Vertex K)
    (hab : (incidence K).Adj a b) (hbc : (incidence K).Adj b c)
    (hcd : (incidence K).Adj c d) (hda : (incidence K).Adj d a) :
    a = c ∨ b = d := by
  cases a with
  | inl p =>
    cases b with
    | inl l => exact False.elim hab
    | inr l =>
      cases c with
      | inr r => exact False.elim hbc
      | inl r =>
        cases d with
        | inl s => exact False.elim hcd
        | inr s =>
          simpa using rectangle p r l s hab hda hbc hcd
  | inr l =>
    cases b with
    | inr p => exact False.elim hab
    | inl p =>
      cases c with
      | inl s => exact False.elim hbc
      | inr s =>
        cases d with
        | inr r => exact False.elim hcd
        | inl r =>
          simpa [or_comm] using rectangle p r l s hab hbc hda hcd

theorem free_three : (cycleGraph 3).Free (incidence K) := by
  rintro ⟨f⟩
  exact no_triangle (f 0) (f 1) (f 2)
    (f.toHom.map_adj (by decide)) (f.toHom.map_adj (by decide))
    (f.toHom.map_adj (by decide))

theorem free_four : (cycleGraph 4).Free (incidence K) := by
  rintro ⟨f⟩
  have h := no_rectangle (f 0) (f 1) (f 2) (f 3)
    (f.toHom.map_adj (by decide)) (f.toHom.map_adj (by decide))
    (f.toHom.map_adj (by decide)) (f.toHom.map_adj (by decide))
  rcases h with h | h
  · have := f.injective h
    norm_num at this
  · have := f.injective h
    norm_num at this

variable [Fintype K] [DecidableEq K]

theorem degree_point (p : K × K) :
    (incidence K).degree (.inl p) = Fintype.card K := by
  classical
  symm
  rw [← Finset.card_univ, ← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun a _ => Sum.inr (a, p.2 - a * p.1))
  · intro a _
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    change p.2 = a * p.1 + (p.2 - a * p.1)
    ring
  · intro a _ b _ h
    exact congrArg Prod.fst (Sum.inr.inj h)
  · intro v hv
    cases v with
    | inl r => exact False.elim ((SimpleGraph.mem_neighborFinset _ _ _).mp hv)
    | inr l =>
      refine ⟨l.1, mem_univ _, ?_⟩
      have hl : p.2 = l.1 * p.1 + l.2 := (SimpleGraph.mem_neighborFinset _ _ _).mp hv
      congr 1
      apply Prod.ext
      · rfl
      · dsimp; linear_combination hl

theorem degree_line (l : K × K) :
    (incidence K).degree (.inr l) = Fintype.card K := by
  classical
  symm
  rw [← Finset.card_univ, ← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun x _ => Sum.inl (x, l.1 * x + l.2))
  · intro x _
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    rfl
  · intro x _ y _ h
    exact congrArg Prod.fst (Sum.inl.inj h)
  · intro v hv
    cases v with
    | inr r => exact False.elim ((SimpleGraph.mem_neighborFinset _ _ _).mp hv)
    | inl p =>
      refine ⟨p.1, mem_univ _, ?_⟩
      have hp : p.2 = l.1 * p.1 + l.2 := (SimpleGraph.mem_neighborFinset _ _ _).mp hv
      apply congrArg Sum.inl
      apply Prod.ext
      · rfl
      · exact hp.symm

theorem regular (v : Vertex K) :
    (incidence K).degree v = Fintype.card K := by
  cases v with
  | inl p => exact degree_point p
  | inr l => exact degree_line l

omit [Field K] [DecidableEq K] in
theorem vertex_count : Fintype.card (Vertex K) = 2 * Fintype.card K ^ 2 := by
  simp [Vertex, Fintype.card_sum, Fintype.card_prod]
  ring

theorem edge_count : (incidence K).edgeFinset.card = Fintype.card K ^ 3 := by
  have h := (incidence K).sum_degrees_eq_twice_card_edges
  simp_rw [regular] at h
  simp only [sum_const, card_univ, smul_eq_mul, vertex_count] at h
  nlinarith

/-- A graph on the standard vertex set with the exact advertised parameters. -/
theorem finite_field_construction :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card K ^ 2)), ∃ _ : DecidableRel G.Adj,
      (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G ∧
      G.edgeFinset.card = Fintype.card K ^ 3 := by
  classical
  let e := Fintype.equivFinOfCardEq (vertex_count (K := K))
  let G := (incidence K).map e
  let iso : incidence K ≃g G := SimpleGraph.Iso.map e (incidence K)
  refine ⟨G, inferInstance, ?_, ?_, ?_⟩
  · exact (free_congr_right iso).mp free_three
  · exact (free_congr_right iso).mp free_four
  · exact iso.card_edgeFinset_eq.symm.trans edge_count

open scoped Classical in
/-- The maximum number of edges avoiding both (not necessarily induced) cycles. -/
noncomputable def exC3C4 (n : ℕ) : ℕ :=
  Finset.sup {G : SimpleGraph (Fin n) |
    (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G} (fun G => G.edgeFinset.card)

theorem finite_field_lower_bound :
    Fintype.card K ^ 3 ≤ exC3C4 (2 * Fintype.card K ^ 2) := by
  classical
  obtain ⟨G, _, h3, h4, he⟩ := finite_field_construction (K := K)
  rw [← he, exC3C4]
  convert! Finset.le_sup (s := {H : SimpleGraph (Fin (2 * Fintype.card K ^ 2)) |
      (cycleGraph 3).Free H ∧ (cycleGraph 4).Free H})
    (f := fun (H : SimpleGraph (Fin (2 * Fintype.card K ^ 2))) => H.edgeFinset.card)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h3, h4⟩)

end JSP000463

namespace JSP000463
open SimpleGraph

/-- The lower bound is available at every prime, without a finite cutoff. -/
theorem prime_lower_bound (p : ℕ) (hp : p.Prime) : p ^ 3 ≤ exC3C4 (2 * p ^ 2) := by
  let : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.card] using finite_field_lower_bound (K := ZMod p)

/-- Arbitrarily large graph orders attain the conjectured lower-bound scale exactly. -/
theorem unbounded_lower_bound (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < 2 * p ^ 2 ∧ p ^ 3 ≤ exC3C4 (2 * p ^ 2) := by
  obtain ⟨p, hN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  refine ⟨p, hp, ?_, prime_lower_bound p hp⟩
  have := hp.two_le
  nlinarith

/-- An exact algebraic version of the conjectured `1/(2 sqrt 2)` lower scale.
This holds for arbitrarily large orders, not a claimed all-order asymptotic. -/
theorem unbounded_graphs (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G ∧
      8 * G.edgeFinset.card ^ 2 = n ^ 3 := by
  obtain ⟨p, hN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨G, inst, h3, h4, he⟩ := finite_field_construction (K := ZMod p)
  refine ⟨2 * Fintype.card (ZMod p) ^ 2, ?_, G, inst, h3, h4, ?_⟩
  · rw [ZMod.card]
    have := hp.two_le
    nlinarith
  · rw [he]
    ring

end JSP000463
