import JSP000746Sharp

/-!
The original integer-graph endpoint for JSP-000746 / Erdős 895.
Our contribution under GitHub account ketianzhang1-lang, with OpenAI assistance,
transports the checked finite result to arbitrary graphs on the integers.
The imported upper-bound proof retains its original attribution.
-/

namespace JSP000746

/-- Every triangle-free graph on the integers has three distinct, positive,
pairwise nonadjacent vertices a, b, a+b, already among labels 1,...,18. -/
theorem integer_graph (G : SimpleGraph ℤ) (hG : G.CliqueFree 3) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ a + b ≤ 18 ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a (a + b) ∧ ¬ G.Adj b (a + b) := by
  let e : Fin 18 ↪ ℤ :=
    ⟨fun i => (i.val : ℤ) + 1, by
      intro i j h
      apply Fin.ext
      dsimp at h
      omega⟩
  let H : SimpleGraph (Fin 18) := G.comap e
  have hH : H.CliqueFree 3 :=
    hG.comap (SimpleGraph.Embedding.comap e G).isContained
  obtain ⟨a, b, hs, hab, h1, h2, h3⟩ := Erdos895.finite_eighteen H hH
  have he : e ⟨a.val + b.val + 1, hs⟩ = e a + e b := by
    change ((a.val + b.val + 1 : ℕ) : ℤ) + 1 =
      ((a.val : ℤ) + 1) + ((b.val : ℤ) + 1)
    push_cast
    ring
  change ¬ G.Adj (e a) (e b) at h1
  change ¬ G.Adj (e a) (e ⟨a.val + b.val + 1, hs⟩) at h2
  change ¬ G.Adj (e b) (e ⟨a.val + b.val + 1, hs⟩) at h3
  rw [he] at h2 h3
  refine ⟨e a, e b, ?_, ?_, ?_, h1, h2, h3⟩
  · change 0 < (a.val : ℤ) + 1
    omega
  · change (a.val : ℤ) + 1 < (b.val : ℤ) + 1
    omega
  · change ((a.val : ℤ) + 1) + ((b.val : ℤ) + 1) ≤ 18
    omega

/-- The catalog's original question with all three distinctness conditions explicit. -/
theorem jsp_000746 (G : SimpleGraph ℤ) (hG : G.CliqueFree 3) :
    ∃ a b c : ℤ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ c = a + b ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := by
  obtain ⟨a, b, ha, hab, _, h1, h2, h3⟩ := integer_graph G hG
  exact ⟨a, b, a + b, by omega, by omega, by omega, rfl, h1, h2, h3⟩

end JSP000746
