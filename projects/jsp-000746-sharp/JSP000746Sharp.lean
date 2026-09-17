import Erdos895

/-!
Sharpness supplement for JSP-000746 / Erdos 895.
The upper bound is imported unchanged from the pinned plby formalization,
which credits Ben Barber (mathematics), Codex and GPT-5.6 Sol (formalization).
The 17-vertex witness was obtained independently by an integer feasibility
search and is checked below by Lean kernel reduction, not by trusting that solver.
Prepared with OpenAI ChatGPT assistance. No mathematical novelty is asserted.
-/

namespace JSP000746Sharp

set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

/-- Zero-based endpoints; mathematical vertex labels are `i.val + 1`. -/
def edges : List (Fin 17 × Fin 17) := [
  (0,2), (0,4), (0,6), (0,10), (0,12), (0,14),
  (1,4), (1,5), (1,9), (1,12), (1,13),
  (2,5), (2,7), (2,9), (2,11),
  (3,6), (3,9), (3,10), (3,11), (3,12),
  (4,8), (4,11), (5,6), (5,10), (5,14),
  (6,8), (6,16), (7,8), (7,12), (7,13), (7,14),
  (8,9), (8,10), (9,14), (9,15), (10,13), (10,15),
  (11,13), (11,15), (12,15), (13,16), (14,16), (15,16)]

def adj (a b : Fin 17) : Prop := (a,b) ∈ edges ∨ (b,a) ∈ edges

instance : DecidableRel adj := fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ edges ∨ (b,a) ∈ edges))

def witness : SimpleGraph (Fin 17) where
  Adj := adj
  symm := by intro a b h; exact h.elim Or.inr Or.inl
  loopless := by decide

instance : DecidableRel witness.Adj := inferInstanceAs (DecidableRel adj)

/-- Every ordered triple is checked, including repeated vertices. -/
theorem no_triangles : ∀ a b c : Fin 17,
    ¬ (witness.Adj a b ∧ witness.Adj a c ∧ witness.Adj b c) := by
  decide

/-- Every distinct-summand Schur triple contains at least one edge. -/
theorem schur_coverage : ∀ a b c : Fin 17,
    a.val < b.val → a.val + b.val + 1 = c.val →
      witness.Adj a b ∨ witness.Adj a c ∨ witness.Adj b c := by
  decide

theorem witness_triangle_free : witness.CliqueFree 3 := by
  intro s hs
  obtain ⟨a,b,c,_,_,_,rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  exact no_triangles a b c (SimpleGraph.is3Clique_triple_iff.mp hs)

theorem witness_no_independent_schur_triple :
    ¬ Erdos895.HasIndependentSchurTriple witness := by
  rintro ⟨a,b,hs,hab,h1,h2,h3⟩
  rcases schur_coverage a b ⟨a.val+b.val+1,hs⟩ hab rfl with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

/-- The same witness restricted to the initial interval handles every n <= 17. -/
theorem counterexamples_below_eighteen {n : ℕ} (hn : n ≤ 17) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
      ¬ Erdos895.HasIndependentSchurTriple G := by
  let f : Fin n ↪ Fin 17 := Fin.castLEEmb hn
  let H : SimpleGraph (Fin n) := witness.comap f
  have hH : H.CliqueFree 3 :=
    witness_triangle_free.comap (SimpleGraph.Embedding.comap f witness).isContained
  refine ⟨H,hH,?_⟩
  rintro ⟨a,b,hs,hab,h1,h2,h3⟩
  apply witness_no_independent_schur_triple
  have hs17 : (f a).val + (f b).val + 1 < 17 := by
    change a.val + b.val + 1 < 17
    omega
  exact ⟨f a,f b,hs17,hab,h1,h2,h3⟩

/-- Precisely the graph-theoretic property in the original distinct-vertex problem. -/
def Forcing (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    Erdos895.HasIndependentSchurTriple G

/-- Full threshold equivalence: not merely an example or a sufficient bound. -/
theorem exact_threshold (n : ℕ) : Forcing n ↔ 18 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hn17 : n ≤ 17 := by omega
    obtain ⟨G,hG,hno⟩ := counterexamples_below_eighteen hn17
    exact hno (h G hG)
  · intro hn G hG
    exact Erdos895.explicit_bound hn G hG

theorem least_threshold : Forcing 18 ∧ ∀ n : ℕ, Forcing n → 18 ≤ n := by
  exact ⟨(exact_threshold 18).mpr (by omega), fun n h => (exact_threshold n).mp h⟩

#print axioms no_triangles
#print axioms schur_coverage
#print axioms witness_triangle_free
#print axioms witness_no_independent_schur_triple
#print axioms counterexamples_below_eighteen
#print axioms exact_threshold
#print axioms least_threshold

end JSP000746Sharp
