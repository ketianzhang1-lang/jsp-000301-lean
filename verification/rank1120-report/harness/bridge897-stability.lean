import JSP000897Stability

namespace Verify897Stability

open Classical in
/-- Non-strict catalog threshold, expressed solely with Mathlib's extremal number,
undirected edge sets, adjacency, degree and set cardinality. -/
theorem catalog_threshold {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) ≤ Nat.card G.edgeSet) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) ≤
        {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard := by
  classical
  simpa only [Erdos1079.cliqueExtremalNumber, Erdos1079.edgeCount,
    Erdos1079.linkEdgeCount] using Erdos1079.erdos_problem_1079 hr hn G hG

open Classical in
/-- Erdős's 1975 convention is f_r(n)=ex(n,K_r)+1, not ex(n,K_r).
The strict endpoint gives exactly that local forcing threshold. -/
theorem forcing_threshold {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) + 1 ≤ Nat.card G.edgeSet) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧ n < 4 * G.degree v ∧
      SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) + 1 ≤
        {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard := by
  classical
  have hstrict : Erdos1079.cliqueExtremalNumber n r < Erdos1079.edgeCount G := by
    change SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) < Nat.card G.edgeSet
    omega
  obtain ⟨v, hv, hd, he⟩ := JSP000897.strict_resolution hr hn G hstrict
  refine ⟨v, hv, by omega, ?_⟩
  change Erdos1079.cliqueExtremalNumber (G.degree v) (r - 1) + 1 ≤
    Erdos1079.linkEdgeCount G v
  omega

open Classical in
/-- One absolute positive constant works for every r, so in particular c_r exists. -/
theorem uniform_linear_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, 2 ≤ n →
      ∀ G : SimpleGraph (Fin n),
      SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) + 1 ≤ Nat.card G.edgeSet →
      ∃ v : Fin n, c * (n : ℝ) < (G.degree v : ℝ) ∧
        SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) + 1 ≤
          {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard := by
  classical
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro r hr n hn G hG
  obtain ⟨v, _, hd, he⟩ := forcing_threshold hr hn G hG
  refine ⟨v, ?_, he⟩
  have hd' : (n : ℝ) < 4 * (G.degree v : ℝ) := by exact_mod_cast hd
  nlinarith

open Classical in
/-- The submitter's extra integral surplus assertion at every maximum-degree vertex. -/
theorem every_maximum_surplus {n r s : ℕ} (hr : 4 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) + s ≤ Nat.card G.edgeSet)
    (v : Fin n) (hv : G.degree v = G.maxDegree) :
    SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) + s ≤
      {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard := by
  classical
  simpa only [Erdos1079.cliqueExtremalNumber, Erdos1079.edgeCount,
    Erdos1079.linkEdgeCount] using JSP000897.surplus_at_every_maximum hr G hG v hv


open Classical in
/-- Degree-deficit extension uses the actual graph maximum and includes r=3. -/
theorem degree_deficit {n r s δ : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) + s ≤ Nat.card G.edgeSet)
    (v : Fin n) (hv : G.maxDegree ≤ G.degree v + δ) :
    SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) + s ≤
      {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard +
        δ * (n - G.degree v) := by
  classical
  simpa only [Erdos1079.cliqueExtremalNumber, Erdos1079.edgeCount,
    Erdos1079.linkEdgeCount] using JSP000897.surplus_with_degree_deficit hr G hG v hv

open Classical in
/-- Recover surplus at every maximum-degree vertex including the triangle threshold. -/
theorem every_maximum_from_three {n r s : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n))
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) + s ≤ Nat.card G.edgeSet)
    (v : Fin n) (hv : G.degree v = G.maxDegree) :
    SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) + s ≤
      {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard := by
  classical
  simpa only [Erdos1079.cliqueExtremalNumber, Erdos1079.edgeCount,
    Erdos1079.linkEdgeCount] using JSP000897.surplus_at_every_maximum_from_three hr G hG v hv

end Verify897Stability
