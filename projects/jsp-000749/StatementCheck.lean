import JSP000749

/-!
A plain-quantifier endpoint, written separately from the implementation definitions.
This is a contributor-written semantic adapter, not independent human certification.
-/
namespace JSP000749StatementCheck

theorem plain_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ H : Finset (Finset (Fin (2 * n ^ 2))),
      (∀ e ∈ H, e.card = n) ∧ H.card ≤ 4 * n ^ 2 * 2 ^ n ∧
      (∃ c : Fin (2 * n ^ 2) → Fin 3,
        ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v) ∧
      (∀ c : Fin (2 * n ^ 2) → Fin 2,
        ∃ e ∈ H, ∀ u ∈ e, ∀ v ∈ e, c u = c v) := by
  classical
  obtain ⟨H, hU, hcard, h3, _⟩ := JSP000749.jsp000749_upper_bound n hn
  refine ⟨H, hU, hcard, h3.1, ?_⟩
  have hh := h3.2 2 (by decide)
  unfold JSP000749.Colorable at hh
  push Not at hh
  exact hh

/-- A genuine two-vertex edge is two-colourable. -/
example : JSP000749.Colorable ({{0, 1}} : Finset (Finset (Fin 2))) 2 := by
  refine ⟨id, ?_⟩
  intro e he
  have he' : e = {0, 1} := by simpa using he
  subst e
  exact ⟨0, by simp, 1, by simp, by decide⟩

/-- A singleton edge cannot be properly coloured with any number of colours.
This shows why the n>=2 side condition matters. -/
example (k : ℕ) : ¬ JSP000749.Colorable ({{0}} : Finset (Finset (Fin 1))) k := by
  rintro ⟨c, hc⟩
  obtain ⟨u, hu, v, hv, hne⟩ := hc {0} (by simp)
  have hu' : u = 0 := by simpa using hu
  have hv' : v = 0 := by simpa using hv
  exact hne (by rw [hu', hv'])

#print axioms plain_upper_bound
end JSP000749StatementCheck
