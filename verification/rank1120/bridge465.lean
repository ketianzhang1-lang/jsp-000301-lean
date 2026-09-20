import JSP000465

namespace Verify465
open Erdos180 Filter
open scoped Classical

/-- Maximum edge count over every labelled host of order n, excluding every
forbidden member by ordinary Mathlib subgraph containment. -/
noncomputable def literalExtremal (F : Finset FiniteGraph) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    ∀ H ∈ F, H.graph.Free G).sup (fun G => G.edgeFinset.card)

theorem extremal_formula (F : Finset FiniteGraph) (n : ℕ) :
    familyExtremal F n = literalExtremal F n := rfl

theorem singleton_literal (H : FiniteGraph) (n : ℕ) :
    literalExtremal {H} n = SimpleGraph.extremalNumber n H.graph :=
  JSP000465.familyExtremal_singleton H n

/-- Every order, including zero, has a real admissible maximizing host. -/
theorem extremal_attained_literal (n : ℕ) :
    ∃ G : SimpleGraph (Fin n),
      (∀ H ∈ proposedFamily, H.graph.Free G) ∧
      G.edgeFinset.card = literalExtremal proposedFamily n :=
  JSP000465.familyExtremal_attained n

/-- The eventual threshold is chosen after the constant, and before the host
order and forbidden member. This is the simultaneous all-orders statement. -/
theorem connected_cyclic_counterexample_literal :
    ∃ F : Finset FiniteGraph, F.Nonempty ∧
      (∀ H ∈ F, H.graph.Connected ∧ H.graph.IsBipartite ∧ ¬ H.graph.IsAcyclic) ∧
      ∀ K : ℝ, 0 < K → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H ∈ F,
        K * (literalExtremal F n : ℝ) <
          (SimpleGraph.extremalNumber n H.graph : ℝ) := by
  obtain ⟨F, hne, hshape, hsep⟩ := JSP000465.connected_bipartite_counterexample
  refine ⟨F, hne, hshape, ?_⟩
  intro K hK
  exact Filter.eventually_atTop.mp (hsep K hK)

/-- The stronger corrected compactness conjecture, which excludes forests,
is also refuted; the witness has connected bipartite cyclic members. -/
theorem corrected_compactness_false_literal :
    ¬ (∀ F : Finset FiniteGraph, F.Nonempty →
      (∀ H ∈ F, ¬ H.graph.IsAcyclic) →
      ∃ H ∈ F, ∃ K : ℝ, 0 < K ∧
        ∀ᶠ n : ℕ in atTop,
          (SimpleGraph.extremalNumber n H.graph : ℝ) ≤
            K * (literalExtremal F n : ℝ)) :=
  Erdos180.not_erdos_180_source

/-- The catalog's weaker bipartite-member formulation is refuted as well. -/
theorem bipartite_compactness_false_literal :
    ¬ (∀ F : Finset FiniteGraph, F.Nonempty →
      (∃ H ∈ F, H.graph.IsBipartite) →
      ∃ H ∈ F, ∃ K : ℝ, 0 < K ∧
        ∀ᶠ n : ℕ in atTop,
          (SimpleGraph.extremalNumber n H.graph : ℝ) ≤
            K * (literalExtremal F n : ℝ)) :=
  JSP000465.not_bipartite_compactness

end Verify465
