import JSP000907Complete

namespace Verify907
open SimpleGraph Filter

/-- Chords are distinct unordered ambient edges joining cycle vertices and
absent from the walk's cycle edges; the predicate is Mathlib's IsChord. -/
noncomputable def literalChordCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : ℕ := by
  classical
  exact (G.edgeFinset.filter fun e => p.IsChord e).card

theorem chord_count_formula {V : Type*} [Fintype V]
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    Erdos1091.Walk.chordCount p = literalChordCount p := rfl

/-- The first original question, for arbitrary finite vertex types. -/
theorem affirmative_literal {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfour : G.chromaticNumber = (4 : ℕ∞)) (hfree : G.CliqueFree 4) :
    ∃ (u : V) (p : G.Walk u u),
      p.IsCycle ∧ Odd p.length ∧ 2 ≤ literalChordCount p :=
  JSP000907.affirmative G hfour hfree

/-- A witness for every cutoff, with the small-subgraph hypothesis expanded
literally. Edge-deleted subgraphs are included. The cap holds for all cycles. -/
theorem counterexample_literal (r : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      r < n ∧ n ≤ r + 31 ∧
      G.chromaticNumber = (4 : ℕ∞) ∧ G.CliqueFree 4 ∧
      (∀ H : G.Subgraph, H.verts.ncard ≤ r → H.coe.Colorable 3) ∧
      (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → literalChordCount p ≤ 10) :=
  JSP000907.explicit_counterexample r

/-- A quantitative guarantee is pointwise bounded for arbitrary real-valued
functions, without monotonicity, integrality or convergence assumptions. -/
theorem any_guarantee_bounded (f : ℕ → ℝ)
    (hf : ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber = (4 : ℕ∞) →
      (∀ H : G.Subgraph, H.verts.ncard ≤ r → H.coe.Colorable 3) →
      ∃ (u : Fin n) (p : G.Walk u u),
        p.IsCycle ∧ Odd p.length ∧ f r ≤ (literalChordCount p : ℝ)) :
    ∀ r : ℕ, f r ≤ 10 :=
  JSP000907.realGuarantee_le_ten hf

/-- The second original question is false with the literal all-subgraph
quantifiers and the real limit condition retained. -/
theorem no_diverging_guarantee_literal :
    ¬ ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
        G.chromaticNumber = (4 : ℕ∞) →
        (∀ H : G.Subgraph, H.verts.ncard ≤ r → H.coe.Colorable 3) →
        ∃ (u : Fin n) (p : G.Walk u u),
          p.IsCycle ∧ Odd p.length ∧ f r ≤ (literalChordCount p : ℝ) :=
  JSP000907.no_diverging_realGuarantee

end Verify907
