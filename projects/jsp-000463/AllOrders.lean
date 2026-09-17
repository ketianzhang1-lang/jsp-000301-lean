import JSP000463
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Sqrt

/-!
All-order lower bound supplement for JSP-000463 / Erdos 573.
This formalizes a classical consequence of the finite-field construction and
Bertrand's postulate. It does not settle the conjectured asymptotic constant.
-/

namespace JSP000463
open Finset SimpleGraph

/-- Adding isolated vertices cannot introduce a copy of a graph without isolated vertices. -/
theorem free_map_of_no_isolated {U V W : Type*} {H : SimpleGraph U}
    {G : SimpleGraph V} (e : V ↪ W) (hH : ∀ u, ∃ v, H.Adj u v)
    (hG : H.Free G) : H.Free (G.map e) := by
  classical
  rintro ⟨f⟩
  have hpre : ∀ u, ∃ v, e v = f u := by
    intro u
    obtain ⟨w, huw⟩ := hH u
    obtain ⟨v, z, _, hv, _⟩ := (SimpleGraph.map_adj e G _ _).mp (f.toHom.map_adj huw)
    exact ⟨v, hv⟩
  let g : U → V := fun u => Classical.choose (hpre u)
  have hg (u : U) : e (g u) = f u := Classical.choose_spec (hpre u)
  apply hG
  refine ⟨{ toHom := ⟨g, ?_⟩, injective' := ?_ }⟩
  · intro u v huv
    have hadj := f.toHom.map_adj huv
    change (G.map e).Adj (f u) (f v) at hadj
    rw [← hg u, ← hg v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    apply f.injective
    change f u = f v
    change g u = g v at huv
    rw [← hg u, ← hg v, huv]

/-- A precise padding lemma: edge count and both forbidden ordinary cycles are preserved. -/
theorem pad_graph {m n : ℕ} (hmn : m ≤ n) (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (h3 : (cycleGraph 3).Free G) (h4 : (cycleGraph 4).Free G) :
    ∃ H : SimpleGraph (Fin n), ∃ _ : DecidableRel H.Adj,
      (cycleGraph 3).Free H ∧ (cycleGraph 4).Free H ∧
      H.edgeFinset.card = G.edgeFinset.card := by
  classical
  let e := Fin.castLEEmb hmn
  refine ⟨G.map e, inferInstance, ?_, ?_, ?_⟩
  · exact free_map_of_no_isolated e (by decide) h3
  · exact free_map_of_no_isolated e (by decide) h4
  · convert! card_edgeFinset_map e G

/-- Each admissible graph contributes a lower bound to the extremal number. -/
theorem edge_count_le_ex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : (cycleGraph 3).Free G) (h4 : (cycleGraph 4).Free G) :
    G.edgeFinset.card ≤ exC3C4 n := by
  classical
  unfold exC3C4
  convert! Finset.le_sup (s := {H : SimpleGraph (Fin n) |
      (cycleGraph 3).Free H ∧ (cycleGraph 4).Free H})
    (f := fun (H : SimpleGraph (Fin n)) => H.edgeFinset.card)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h3, h4⟩)

/-- The extremal number is monotone in the number of vertices. -/
theorem exC3C4_monotone : Monotone exC3C4 := by
  classical
  intro m n hmn
  rw [exC3C4, Finset.sup_le_iff]
  intro G hG
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
  obtain ⟨H, _, h3, h4, he⟩ := pad_graph hmn G hG.1 hG.2
  rw [← he]
  exact edge_count_le_ex H h3 h4

/-- Bertrand supplies a field size that fits inside every order `n ≥ 8`. -/
theorem prime_for_order (n : ℕ) (hn : 8 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 2 * p ^ 2 ≤ n ∧ n < 8 * p ^ 2 := by
  let k := Nat.sqrt (n / 8)
  have hk : k ≠ 0 := by
    have hd : 1 ≤ n / 8 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    have hks : 1 ≤ k := Nat.le_sqrt'.mpr (by simpa using hd)
    omega
  obtain ⟨p, hp, hkp, hpk⟩ := Nat.exists_prime_lt_and_le_two_mul k hk
  have hlow : k ^ 2 ≤ n / 8 := Nat.sqrt_le' _
  have hhigh : n / 8 < (k + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hfit : 8 * k ^ 2 ≤ n := by
    have := (Nat.le_div_iff_mul_le (by decide)).mp hlow
    nlinarith
  have hclose : n < 8 * (k + 1) ^ 2 := by
    have := (Nat.div_lt_iff_lt_mul (by decide)).mp hhigh
    nlinarith
  refine ⟨p, hp, ?_, ?_⟩
  · have : p ^ 2 ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left hpk 2
    nlinarith
  · have : (k + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hkp 2
    nlinarith

/-- For every `n ≥ 8`, there is an `n`-vertex graph with no triangles or four-cycles
and more than `n^(3/2) / (16 sqrt 2)` edges, stated without radicals. -/
theorem all_order_graphs (n : ℕ) (hn : 8 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G ∧
      n ^ 3 < 512 * G.edgeFinset.card ^ 2 := by
  obtain ⟨p, hp, hfit, hclose⟩ := prime_for_order n hn
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨G, _, h3, h4, he⟩ := finite_field_construction (K := ZMod p)
  have hsize : 2 * Fintype.card (ZMod p) ^ 2 ≤ n := by simpa only [ZMod.card] using hfit
  obtain ⟨H, inst, hH3, hH4, hHedge⟩ := pad_graph hsize G h3 h4
  refine ⟨H, inst, hH3, hH4, ?_⟩
  rw [hHedge, he, ZMod.card]
  have hpow : n ^ 3 < (8 * p ^ 2) ^ 3 := Nat.pow_lt_pow_left hclose (by decide)
  convert hpow using 1
  ring

/-- A fully quantified uniform lower bound, not a claim about the sharp asymptotic constant. -/
theorem all_order_lower_bound (n : ℕ) (hn : 8 ≤ n) :
    n ^ 3 < 512 * exC3C4 n ^ 2 := by
  obtain ⟨G, _, h3, h4, h⟩ := all_order_graphs n hn
  have hle := Nat.pow_le_pow_left (edge_count_le_ex G h3 h4) 2
  exact h.trans_le (Nat.mul_le_mul_left 512 hle)

end JSP000463
