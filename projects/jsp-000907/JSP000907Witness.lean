/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import JSP000907OddRim
import ErdosProblems.Erdos1091

namespace JSP000907
open SimpleGraph

/-- The nine-cycle appearing in our original odd-rim note. -/
def nineCycle (m : ℕ) : (oddRimGraph m).Walk none none :=
  .cons (show (oddRimGraph m).Adj none (some (0, 2)) from by
    change 2 ≤ (2 : Fin 4).val; decide)
  (.cons (show (oddRimGraph m).Adj (some (0, 2)) (some (0, 3)) from
    Or.inr ⟨rfl, by decide⟩)
  (.cons (show (oddRimGraph m).Adj (some (0, 3)) (some (0, 1)) from
    Or.inr ⟨rfl, by decide⟩)
  (.cons (show (oddRimGraph m).Adj (some (0, 1)) (some (0, 0)) from
    Or.inr ⟨rfl, by decide⟩)
  (.cons (show (oddRimGraph m).Adj (some (0, 0)) (some (1, 0)) from
    Or.inl ⟨rfl, rfl, by
      apply cycleGraph_adj'.mpr
      right
      simp⟩)
  (.cons (show (oddRimGraph m).Adj (some (1, 0)) (some (1, 1)) from
    Or.inr ⟨rfl, by decide⟩)
  (.cons (show (oddRimGraph m).Adj (some (1, 1)) (some (1, 3)) from
    Or.inr ⟨rfl, by decide⟩)
  (.cons (show (oddRimGraph m).Adj (some (1, 3)) (some (1, 2)) from
    Or.inr ⟨rfl, by decide⟩)
  (.cons (show (oddRimGraph m).Adj (some (1, 2)) none from by
    change 2 ≤ (2 : Fin 4).val; decide) .nil))))))))

theorem nineCycle_length (m : ℕ) : (nineCycle m).length = 9 := rfl

theorem nineCycle_isCycle (m : ℕ) : (nineCycle m).IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · simp [nineCycle, Walk.cons_isPath_iff]
  · rw [nineCycle_length]; decide

def fourChords (m : ℕ) : Finset (Sym2 (OddRimVertex m)) :=
  {s(none, some (0, 3)), s(none, some (1, 3)),
   s(some (0, 1), some (0, 2)), s(some (1, 1), some (1, 2))}

theorem fourChords_card (m : ℕ) : (fourChords m).card = 4 := by
  simp [fourChords]

theorem fourChords_subset (m : ℕ) :
    fourChords m ⊆ Erdos1091.Walk.chordFinset (nineCycle m) := by
  intro e he
  simp only [fourChords, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [Erdos1091.Walk.mem_chordFinset, Walk.isChord_sym2Mk, nineCycle,
      Walk.edges_cons, Walk.edges_nil, Walk.support_cons, Walk.support_nil] <;>
    simp [oddRimGraph, Construction.graph, Construction.adjacent,
      Construction.localAdj]

theorem nineCycle_four_chords (m : ℕ) :
    (nineCycle m).IsCycle ∧ Odd (nineCycle m).length ∧
      4 ≤ Erdos1091.Walk.chordCount (nineCycle m) := by
  refine ⟨nineCycle_isCycle m, ?_, ?_⟩
  · rw [nineCycle_length]
    decide
  · change 4 ≤ (Erdos1091.Walk.chordFinset (nineCycle m)).card
    calc
      4 = (fourChords m).card := (fourChords_card m).symm
      _ ≤ (Erdos1091.Walk.chordFinset (nineCycle m)).card :=
        Finset.card_le_card (fourChords_subset m)

end JSP000907
