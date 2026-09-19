/-
Copyright (c) 2026 ketianzhang1-lang. Released under Apache 2.0.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance.

Degree-deficit stability for the dense-neighbourhood theorem. The edge-charging
and Turan-splitting arguments below are adapted from the credited Erdos1079
development (Codex / GPT-5.6 Sol; mathematics of Bollobas, Thomason and Bondy).
Our extension keeps the maximum degree separate from the chosen vertex degree,
quantifies the resulting surplus loss, and includes the triangle threshold.
No new mathematical discovery or global first-formalization claim is made.
-/
import JSP000897

namespace JSP000897
open Erdos1079 Finset Fintype

/-- Credited edge charging with the maximum degree retained as a separate bound. -/
theorem edge_bound_by_maxDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    edgeCount G ≤ linkEdgeCount G v +
      G.maxDegree * (Fintype.card V - G.degree v) := by
  classical
  let A := G.neighborFinset v
  let B := Aᶜ
  let inside := {e ∈ G.edgeFinset | e.toFinset ⊆ A}
  let outside := G.edgeFinset \ inside
  have hinside : inside ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have houtside : outside ⊆ B.biUnion fun x => G.incidenceFinset x := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have hnsub : ¬e.toFinset ⊆ A := by
      intro hsub
      exact he'.2 (Finset.mem_filter.mpr ⟨he'.1, hsub⟩)
    rw [Finset.not_subset] at hnsub
    obtain ⟨x, hxe, hxA⟩ := hnsub
    rw [Finset.mem_biUnion]
    refine ⟨x, ?_, ?_⟩
    · simpa [B] using hxA
    · rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨he'.1, Sym2.mem_toFinset.mp hxe⟩
  have houtside : #outside ≤ (Fintype.card V - G.degree v) * G.maxDegree := by
    calc
      #outside ≤ #(B.biUnion fun x => G.incidenceFinset x) := Finset.card_le_card houtside
      _ ≤ ∑ x ∈ B, #(G.incidenceFinset x) := Finset.card_biUnion_le
      _ = ∑ x ∈ B, G.degree x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact G.card_incidenceFinset_eq_degree x
      _ ≤ ∑ _x ∈ B, G.maxDegree := by
        apply Finset.sum_le_sum
        intro x hx
        exact G.degree_le_maxDegree x
      _ = #B * G.maxDegree := by simp
      _ = (Fintype.card V - G.degree v) * G.maxDegree := by
        have hB : #B = Fintype.card V - G.degree v := by
          rw [show B = Aᶜ from rfl, Finset.card_compl]
          simp only [A, SimpleGraph.card_neighborFinset_eq_degree]
        rw [hB]
  have hdecomp : #outside + #inside = #G.edgeFinset := by
    simpa [outside] using Finset.card_sdiff_add_card_eq_card hinside
  have hinternal : #inside = linkEdgeCount G v := by
    simpa [inside, A] using card_internal_neighbor_edges G v
  have houtside' : #outside ≤ G.maxDegree * (Fintype.card V - G.degree v) := by
    simpa [Nat.mul_comm] using houtside
  rw [edgeCount_eq_card_edgeFinset]
  omega

/-- The credited Turan splitting construction also works when r = 3. -/
theorem cliqueExtremal_split_from_three {n d r : ℕ} (hr : 3 ≤ r) (hd : d ≤ n) :
    cliqueExtremalNumber d (r - 1) + d * (n - d) ≤ cliqueExtremalNumber n r := by
  let _ : Nontrivial (Fin (r - 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let _ : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  unfold cliqueExtremalNumber
  rw [SimpleGraph.extremalNumber_top (n := d) (α := Fin (r - 1)),
    SimpleGraph.extremalNumber_top (n := n) (α := Fin r)]
  have hcardr₁ : Fintype.card (Fin (r - 1)) = r - 1 := by
    rw [← Nat.card_eq_fintype_card]
    simp
  have hcardr : Fintype.card (Fin r) = r := by
    rw [← Nat.card_eq_fintype_card]
    simp
  rw [hcardr₁, hcardr]
  exact turan_split_le (q := r - 1) (by omega) hd

open Classical in
/-- A vertex within δ of maximum degree loses at most δ(n-d) of the edge surplus. -/
theorem surplus_with_degree_deficit {n r s δ : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r + s ≤ edgeCount G)
    (v : Fin n) (hv : G.maxDegree ≤ G.degree v + δ) :
    cliqueExtremalNumber (G.degree v) (r - 1) + s ≤
      linkEdgeCount G v + δ * (n - G.degree v) := by
  classical
  have hd : G.degree v ≤ n := by simpa using (G.degree_lt_card_verts v).le
  have he := edge_bound_by_maxDegree G v
  simp only [Fintype.card_fin] at he
  have ht := cliqueExtremal_split_from_three hr hd
  have hm := Nat.mul_le_mul_right (n - G.degree v) hv
  rw [Nat.add_mul] at hm
  omega

open Classical in
/-- The corresponding loss bound on nonnegative integral surplus counts. -/
theorem surplus_loss_bound {n r s δ : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r + s ≤ edgeCount G)
    (v : Fin n) (hv : G.maxDegree ≤ G.degree v + δ) :
    s - δ * (n - G.degree v) ≤
      linkEdgeCount G v - cliqueExtremalNumber (G.degree v) (r - 1) := by
  have h := surplus_with_degree_deficit hr G hG v hv
  omega

open Classical in
/-- Strict localization survives every degree deficit whose penalty is below s. -/
theorem strict_link_with_degree_deficit {n r s δ : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r + s ≤ edgeCount G)
    (v : Fin n) (hv : G.maxDegree ≤ G.degree v + δ)
    (hs : δ * (n - G.degree v) < s) :
    cliqueExtremalNumber (G.degree v) (r - 1) < linkEdgeCount G v := by
  have h := surplus_with_degree_deficit hr G hG v hv
  omega

open Classical in
/-- The zero-deficit case retains all surplus for every r >= 3. -/
theorem surplus_at_every_maximum_from_three {n r s : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r + s ≤ edgeCount G)
    (v : Fin n) (hv : G.degree v = G.maxDegree) :
    cliqueExtremalNumber (G.degree v) (r - 1) + s ≤ linkEdgeCount G v := by
  have h := surplus_with_degree_deficit (δ := 0) hr G hG v (by omega)
  simpa using h

open Classical in
/-- Preserve the complete original endpoint and add robust localization at every
approximately maximum-degree vertex. -/
theorem complete_with_stability {n r s : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : cliqueExtremalNumber n r + s ≤ edgeCount G) :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      cliqueExtremalNumber (G.degree v) (r - 1) +
        (edgeCount G - cliqueExtremalNumber n r) ≤ linkEdgeCount G v) ∧
    (∀ (v : Fin n) (δ : ℕ), G.maxDegree ≤ G.degree v + δ →
      cliqueExtremalNumber (G.degree v) (r - 1) + s ≤
        linkEdgeCount G v + δ * (n - G.degree v)) := by
  refine ⟨resolution_with_surplus hr hn G (by omega), ?_⟩
  intro v δ hv
  exact surplus_with_degree_deficit (by omega) G hG v hv

end JSP000897
