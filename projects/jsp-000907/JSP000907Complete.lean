/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import ErdosProblems.Erdos1091
import JSP000907Witness

/-!
Full JSP-000907 endpoint with explicit statement bridges.
Voss's affirmative theorem and the APSSV bounded-chord counterexamples are
reused from the pinned upstream formalization with their original credits.
Our new work relates induced and arbitrary small subgraphs, handles real
threshold functions without a monotonicity assumption, supplies explicit
counterexample orders, and combines these with our own color-forcing family.
-/

namespace JSP000907
open SimpleGraph Filter

/-- The original local hypothesis, stated for every subgraph, including
subgraphs obtained by deleting edges as well as vertices. -/
def SmallSubgraphsThreeColorable {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ H : G.Subgraph, H.verts.ncard ≤ r → H.coe.Colorable 3

theorem smallSubgraphs_iff_induced {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) :
    SmallSubgraphsThreeColorable G r ↔ Erdos1091.LocallyThreeColorable G r := by
  classical
  constructor
  · intro h s hs
    rw [SimpleGraph.induce_eq_coe_induce_top]
    apply SimpleGraph.Colorable.chromaticNumber_le
    apply h
    simpa using hs
  · intro h H hH
    have hc : (G.induce H.verts).Colorable 3 := by
      have hs : H.verts.toFinset.card ≤ r := by
        rw [← Set.ncard_eq_toFinset_card']
        exact hH
      have hh := h H.verts.toFinset hs
      have heq : (↑H.verts.toFinset : Set V) = H.verts := by
        ext v
        simp only [Finset.mem_coe, Set.mem_toFinset]
      rw [heq] at hh
      exact SimpleGraph.chromaticNumber_le_iff_colorable.mp hh
    apply hc.mono_left
    intro a b hab
    exact H.adj_sub hab

theorem smallSubgraphs_mono {V : Type*} (G : SimpleGraph V) {r s : ℕ}
    (hrs : r ≤ s) (h : SmallSubgraphsThreeColorable G s) :
    SmallSubgraphsThreeColorable G r :=
  fun H hH => h H (hH.trans hrs)

/-- A real-valued quantitative guarantee, with literal subgraph quantifiers. -/
def RealGuarantee (f : ℕ → ℝ) : Prop :=
  ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (4 : ℕ∞) →
    SmallSubgraphsThreeColorable G r →
    ∃ (u : Fin n) (p : G.Walk u u),
      p.IsCycle ∧ Odd p.length ∧ f r ≤ (Erdos1091.Walk.chordCount p : ℝ)

/-- Choosing m=floor(r/20), rather than m=r+1, gives a linear-order
counterexample with an additive overhead of at most 31 vertices. -/
theorem explicit_counterexample (r : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      r < n ∧ n ≤ r + 31 ∧
      G.chromaticNumber = (4 : ℕ∞) ∧ G.CliqueFree 4 ∧
      SmallSubgraphsThreeColorable G r ∧
      (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle →
        Erdos1091.Walk.chordCount p ≤ 10) := by
  let m := r / 20
  have hrem := Nat.mod_lt r (by decide : 0 < 20)
  have hdiv := Nat.mod_add_div r 20
  have hrn : r < 20 * m + 31 := by dsimp [m]; omega
  have hnr : 20 * m + 31 ≤ r + 31 := by dsimp [m]; omega
  refine ⟨20 * m + 31, Erdos1091.Counterexample.finGraph m, hrn, hnr,
    Erdos1091.Counterexample.finGraph_chromatic_four m,
    Erdos1091.Counterexample.finGraph_cliqueFree_four m, ?_, ?_⟩
  · apply (smallSubgraphs_iff_induced _ r).mpr
    exact Erdos1091.Counterexample.finGraph_locallyThreeColorable m r hrn
  · exact Erdos1091.Counterexample.finGraph_cyclesHaveAtMostChords_ten m

/-- Every valid guarantee is pointwise bounded, without any monotonicity
or limit hypothesis. -/
theorem realGuarantee_le_ten {f : ℕ → ℝ} (hf : RealGuarantee f) (r : ℕ) :
    f r ≤ 10 := by
  obtain ⟨n, G, _, _, hfour, _, hlocal, hcycles⟩ := explicit_counterexample r
  obtain ⟨u, p, hp, _, hmany⟩ := hf r n G hfour hlocal
  exact hmany.trans (by exact_mod_cast hcycles u p hp)

theorem realGuarantee_range_bounded {f : ℕ → ℝ} (hf : RealGuarantee f) :
    BddAbove (Set.range f) := by
  refine ⟨10, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact realGuarantee_le_ten hf r

theorem no_unbounded_realGuarantee :
    ¬ ∃ f : ℕ → ℝ, (¬ BddAbove (Set.range f)) ∧ RealGuarantee f := by
  rintro ⟨f, hu, hf⟩
  exact hu (realGuarantee_range_bounded hf)

theorem no_diverging_realGuarantee :
    ¬ ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ RealGuarantee f := by
  rintro ⟨f, hlim, hf⟩
  obtain ⟨r, hr⟩ := (tendsto_atTop_atTop.mp hlim) 11
  have hlo := hr r le_rfl
  have hhi := realGuarantee_le_ten hf r
  linarith

theorem affirmative {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfour : G.chromaticNumber = (4 : ℕ∞)) (hfree : G.CliqueFree 4) :
    ∃ (u : V) (p : G.Walk u u),
      p.IsCycle ∧ Odd p.length ∧ 2 ≤ Erdos1091.Walk.chordCount p :=
  Erdos1091.erdos_1091_affirmative G hfour hfree

/-- The full original problem, retaining its two questions. -/
theorem jsp_000907 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber = (4 : ℕ∞) → G.CliqueFree 4 →
      ∃ (u : Fin n) (p : G.Walk u u),
        p.IsCycle ∧ Odd p.length ∧ 2 ≤ Erdos1091.Walk.chordCount p) ∧
    (¬ ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ RealGuarantee f) :=
  ⟨fun _ G hfour hfree => affirmative G hfour hfree, no_diverging_realGuarantee⟩

/-- The complete original result together with our independently constructed
four-chromatic graphs, for every odd rim order at least three. -/
theorem complete_package :
    ((∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber = (4 : ℕ∞) → G.CliqueFree 4 →
      ∃ (u : Fin n) (p : G.Walk u u),
        p.IsCycle ∧ Odd p.length ∧ 2 ≤ Erdos1091.Walk.chordCount p) ∧
      (¬ ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ RealGuarantee f)) ∧
    (∀ m : ℕ, Fintype.card (OddRimVertex m) = 8 * m + 13 ∧
      (oddRimGraph m).chromaticNumber = (4 : ℕ∞) ∧
      (nineCycle m).IsCycle ∧ Odd (nineCycle m).length ∧
      4 ≤ Erdos1091.Walk.chordCount (nineCycle m)) :=
  ⟨jsp_000907, fun m => ⟨oddRim_card m, oddRim_chromatic_four m,
    nineCycle_four_chords m⟩⟩

end JSP000907
