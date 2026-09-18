/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import JSP000907Construction
import ErdosProblems.Erdos1091.BrooksVertexLemmas

/-! Our uniform odd-rim family. The greedy degree-coloring lemma imported above
retains its upstream credit; the graph and its color-forcing proof are ours. -/

namespace JSP000907
open SimpleGraph

abbrev OddRimVertex (m : ℕ) := Construction.Vertex (Fin (2 * m + 3))
def oddRimGraph (m : ℕ) : SimpleGraph (OddRimVertex m) :=
  Construction.graph (cycleGraph (2 * m + 3))

theorem oddRim_card (m : ℕ) : Fintype.card (OddRimVertex m) = 8 * m + 13 := by
  rw [Construction.card_vertex, Fintype.card_fin]
  omega

theorem cycle_three_colorable (m : ℕ) : (cycleGraph (2 * m + 3)).Colorable 3 := by
  classical
  have hmax : (cycleGraph (2 * m + 3)).maxDegree ≤ 2 := by
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    exact (cycleGraph_degree_three_le (v := v)).le
  exact (cycleGraph (2 * m + 3)).colorable_maxDegree_succ.mono (by omega)

theorem odd_cycle_not_two_colorable (m : ℕ) :
    ¬ (cycleGraph (2 * m + 3)).Colorable 2 := by
  intro h
  have he := (two_colorable_iff_forall_loop_even.mp h) 0 (cycleGraph.cycle (2 * m))
  rw [cycleGraph.length_cycle] at he
  obtain ⟨k, hk⟩ := he
  omega

theorem oddRim_chromatic_four (m : ℕ) :
    (oddRimGraph m).chromaticNumber = (4 : ℕ∞) :=
  Construction.chromatic_four_of_base_three _ (cycle_three_colorable m)
    (odd_cycle_not_two_colorable m)

theorem oddRim_arbitrarily_large (N : ℕ) :
    ∃ m : ℕ, N < Fintype.card (OddRimVertex m) ∧
      (oddRimGraph m).chromaticNumber = (4 : ℕ∞) := by
  exact ⟨N, by rw [oddRim_card]; omega, oddRim_chromatic_four N⟩

end JSP000907
