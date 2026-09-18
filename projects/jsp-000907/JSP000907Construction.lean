/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

/-!
Our odd-rim construction, generalized to an arbitrary base graph.
The local diamond forces the hub color at each attachment, so three-coloring
the construction is equivalent to two-coloring the base. These proofs are
independent of the imported Erdős 1091 development. Chord bounds for this
particular construction are not assumed by any theorem in this file.
-/

namespace JSP000907.Construction
open SimpleGraph

abbrev Vertex (V : Type*) := Option (V × Fin 4)

def localAdj (t s : Fin 4) : Prop :=
  (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨
  (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) ∨
  (t = 1 ∧ s = 3) ∨ (t = 3 ∧ s = 1) ∨
  (t = 2 ∧ s = 3) ∨ (t = 3 ∧ s = 2)

instance : DecidableRel localAdj := fun _ _ => by unfold localAdj; infer_instance

theorem localAdj_symm : ∀ t s, localAdj t s → localAdj s t := by decide
theorem localAdj_irrefl : ∀ t, ¬ localAdj t t := by decide

def adjacent {V : Type*} (G : SimpleGraph V) : Vertex V → Vertex V → Prop
  | none, none => False
  | none, some (_, t) => 2 ≤ t.val
  | some (_, t), none => 2 ≤ t.val
  | some (i, t), some (j, s) =>
      (t = 0 ∧ s = 0 ∧ G.Adj i j) ∨ (i = j ∧ localAdj t s)

def graph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Vertex V) where
  Adj := adjacent G
  symm := by
    constructor
    intro x y h
    cases x with
    | none => cases y <;> exact h
    | some x =>
      cases y with
      | none => exact h
      | some y =>
        rcases h with ⟨ht, hs, hij⟩ | ⟨hij, hts⟩
        · exact Or.inl ⟨hs, ht, hij.symm⟩
        · exact Or.inr ⟨hij.symm, localAdj_symm _ _ hts⟩
  loopless := by
    constructor
    intro x
    cases x with
    | none => exact id
    | some x =>
      rintro (⟨_, _, h⟩ | ⟨_, h⟩)
      · exact G.irrefl h
      · exact localAdj_irrefl _ h

theorem card_vertex (V : Type*) [Fintype V] :
    Fintype.card (Vertex V) = 4 * Fintype.card V + 1 := by
  simp [Vertex, Nat.mul_comm]

theorem attachment_forcing {V : Type*} (G : SimpleGraph V)
    (c : (graph G).Coloring (Fin 3)) (i : V) :
    c (some (i, 1)) = c none := by
  have hab := c.valid (show (graph G).Adj (some (i, 1)) (some (i, 2)) from
    Or.inr ⟨rfl, by decide⟩)
  have hac := c.valid (show (graph G).Adj (some (i, 1)) (some (i, 3)) from
    Or.inr ⟨rfl, by decide⟩)
  have hbc := c.valid (show (graph G).Adj (some (i, 2)) (some (i, 3)) from
    Or.inr ⟨rfl, by decide⟩)
  have hzb := c.valid (show (graph G).Adj none (some (i, 2)) from by
    change 2 ≤ (2 : Fin 4).val; decide)
  have hzc := c.valid (show (graph G).Adj none (some (i, 3)) from by
    change 2 ≤ (3 : Fin 4).val; decide)
  apply Fin.ext
  simp only [ne_eq, Fin.ext_iff] at hab hac hbc hzb hzc
  omega

theorem rim_avoids_hub {V : Type*} (G : SimpleGraph V)
    (c : (graph G).Coloring (Fin 3)) (i : V) :
    c (some (i, 0)) ≠ c none := by
  have h := c.valid (show (graph G).Adj (some (i, 0)) (some (i, 1)) from
    Or.inr ⟨rfl, by decide⟩)
  rwa [attachment_forcing G c i] at h

theorem base_two_colorable_of_three_colorable {V : Type*} (G : SimpleGraph V)
    (h : (graph G).Colorable 3) : G.Colorable 2 := by
  classical
  obtain ⟨c⟩ := h
  let C := {t : Fin 3 // t ≠ c none}
  let d : G.Coloring C := SimpleGraph.Coloring.mk
    (fun i => ⟨c (some (i, 0)), rim_avoids_hub G c i⟩) (by
      intro i j hij heq
      have hc := c.valid (show (graph G).Adj (some (i, 0)) (some (j, 0)) from
        Or.inl ⟨rfl, rfl, hij⟩)
      exact hc (congrArg Subtype.val heq))
  simpa [C] using d.colorable

def fourColor {V : Type*} {G : SimpleGraph V} (c : G.Coloring (Fin 3)) :
    Vertex V → Fin 4
  | none => 0
  | some (i, t) => if t = 0 then ⟨(c i).val + 1, by omega⟩
      else if t = 1 then 0 else if t = 2 then 1 else 2

def fourColoring {V : Type*} {G : SimpleGraph V} (c : G.Coloring (Fin 3)) :
    (graph G).Coloring (Fin 4) := by
  apply SimpleGraph.Coloring.mk (fourColor c)
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => exact hxy.elim
    | some y =>
      rcases y with ⟨i, t⟩
      fin_cases t <;> norm_num [graph, adjacent, fourColor] at *
  | some x =>
    cases y with
    | none =>
      rcases x with ⟨i, t⟩
      fin_cases t <;> norm_num [graph, adjacent, fourColor] at *
    | some y =>
      rcases x with ⟨i, t⟩; rcases y with ⟨j, s⟩
      rcases hxy with ⟨rfl, rfl, hij⟩ | ⟨rfl, hts⟩
      · simpa [fourColor, Fin.ext_iff] using c.valid hij
      · fin_cases t <;> fin_cases s <;>
          norm_num [localAdj, fourColor] at *

theorem chromatic_four_of_base_three {V : Type*} (G : SimpleGraph V)
    (hc : G.Colorable 3) (hn : ¬ G.Colorable 2) :
    (graph G).chromaticNumber = (4 : ℕ∞) := by
  apply (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable).2
  constructor
  · obtain ⟨c⟩ := hc
    exact ⟨fourColoring c⟩
  · exact fun h => hn (base_two_colorable_of_three_colorable G h)

theorem three_colorable_of_base_two_colorable {V : Type*} (G : SimpleGraph V)
    (h : G.Colorable 2) : (graph G).Colorable 3 := by
  obtain ⟨c⟩ := h
  let d : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk
    (fun i => ⟨(c i).val, by omega⟩) (by
      intro i j hij heq
      apply c.valid hij
      exact Fin.ext (congrArg (fun t : Fin 3 => t.val) heq))
  have hbound : ∀ x, (fourColor d x).val < 3 := by
    intro x
    cases x with
    | none => change 0 < 3; decide
    | some x =>
      rcases x with ⟨i, t⟩
      fin_cases t
      · change (c i).val + 1 < 3
        omega
      · change 0 < 3; decide
      · change 1 < 3; decide
      · change 2 < 3; decide
  refine ⟨SimpleGraph.Coloring.mk (fun x => ⟨(fourColor d x).val, hbound x⟩) ?_⟩
  intro x y hxy heq
  apply (fourColoring d).valid hxy
  exact Fin.ext (congrArg (fun t : Fin 3 => t.val) heq)

theorem three_colorable_iff_base_two_colorable {V : Type*} (G : SimpleGraph V) :
    (graph G).Colorable 3 ↔ G.Colorable 2 :=
  ⟨base_two_colorable_of_three_colorable G, three_colorable_of_base_two_colorable G⟩

end JSP000907.Construction
