/-
Copyright (c) 2026. Released under Apache 2.0.
Prepared with OpenAI ChatGPT assistance for the submitting account.
This supplement builds on the credited Erdos1079.lean, ported to Mathlib 4.34.0.
The underlying mathematics is due to Bollobas, Thomason, and Bondy.
No mathematical novelty or first-formalization priority is claimed.
-/
import Erdos1079

namespace JSP000897
open Erdos1079

open Classical in
/-- Every maximum-degree vertex preserves any certified integral edge surplus. -/
theorem surplus_at_every_maximum {n r s : ℕ} (hr : 4 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r + s ≤ edgeCount G)
    (v : Fin n) (hv : G.degree v = G.maxDegree) :
    cliqueExtremalNumber (G.degree v) (r - 1) + s ≤ linkEdgeCount G v := by
  classical
  have hd : G.degree v ≤ n := by
    simpa using (G.degree_lt_card_verts v).le
  have he := maximumDegree_edge_bound G v hv
  have ht := cliqueExtremal_split_le hr hd
  simp only [Fintype.card_fin] at he
  omega

open Classical in
/-- The full non-strict threshold theorem, with the exact integral surplus retained. -/
theorem resolution_with_surplus {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r ≤ edgeCount G) :
    ∃ v : Fin n,
      G.degree v = G.maxDegree ∧
      n ≤ 2 * G.degree v ∧
      cliqueExtremalNumber (G.degree v) (r - 1) +
        (edgeCount G - cliqueExtremalNumber n r) ≤ linkEdgeCount G v := by
  classical
  obtain ⟨v, hv, hd, _⟩ := erdos_problem_1079 hr hn G hG
  refine ⟨v, hv, hd, surplus_at_every_maximum hr G ?_ v hv⟩
  omega

open Classical in
/-- Equivalent comparison of the two nonnegative surplus counts. -/
theorem surplus_dominates {n r : ℕ} (hr : 4 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r ≤ edgeCount G)
    (v : Fin n) (hv : G.degree v = G.maxDegree) :
    edgeCount G - cliqueExtremalNumber n r ≤
      linkEdgeCount G v - cliqueExtremalNumber (G.degree v) (r - 1) := by
  have h := surplus_at_every_maximum (s := edgeCount G - cliqueExtremalNumber n r)
    hr G (by omega) v hv
  omega

open Classical in
/-- Bondy's strict result follows with a surplus of one. -/
theorem strict_resolution {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r < edgeCount G) :
    ∃ v : Fin n,
      G.degree v = G.maxDegree ∧
      n ≤ 2 * G.degree v ∧
      cliqueExtremalNumber (G.degree v) (r - 1) < linkEdgeCount G v := by
  classical
  obtain ⟨v, hv, hd, _⟩ := erdos_problem_1079 hr hn G hG.le
  have hs := surplus_at_every_maximum (s := 1) hr G (by omega) v hv
  exact ⟨v, hv, hd, by omega⟩

end JSP000897
