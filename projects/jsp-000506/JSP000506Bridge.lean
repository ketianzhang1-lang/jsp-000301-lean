/-
Copyright (c) 2026 ketianzhang1-lang. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: ketianzhang1-lang, with OpenAI ChatGPT/Codex assistance
-/
import JSP000506
import Erdos625SelfContained

/-!
We identify our original finite edge-set model with the simple-graph model
of the attributed complete Erdős 625 proof by Samuil Petkov. The imported
proof is unchanged and distributed separately under CC BY 4.0.
-/

namespace JSP000506
open Finset
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

def toGraph {n : ℕ} (s : Finset (Edge n)) : SimpleGraph (Fin n) where
  Adj u v := (∃ h : u < v, (⟨(u,v), h⟩ : Edge n) ∈ s) ∨
    (∃ h : v < u, (⟨(v,u), h⟩ : Edge n) ∈ s)
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro u h; rcases h with ⟨h,_⟩ | ⟨h,_⟩ <;> exact (lt_irrefl u h)⟩

def fromGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Edge n) := by
  classical
  exact univ.filter fun e => G.Adj e.val.1 e.val.2

@[simp] theorem mem_fromGraph {n : ℕ} (G : SimpleGraph (Fin n)) (e : Edge n) :
    e ∈ fromGraph G ↔ G.Adj e.val.1 e.val.2 := by
  classical
  simp [fromGraph]

theorem toGraph_adj_iff {n : ℕ} (s : Finset (Edge n)) {u v : Fin n}
    (h : u < v) : (toGraph s).Adj u v ↔ (⟨(u,v), h⟩ : Edge n) ∈ s := by
  change ((∃ h' : u < v, (⟨(u,v),h'⟩ : Edge n) ∈ s) ∨
    (∃ h' : v < u, (⟨(v,u),h'⟩ : Edge n) ∈ s)) ↔ _
  constructor
  · rintro (⟨_, he⟩ | ⟨h', _⟩)
    · exact he
    · exact (not_lt_of_gt h h').elim
  · intro he; exact Or.inl ⟨h, he⟩

@[simp] theorem fromGraph_toGraph {n : ℕ} (s : Finset (Edge n)) :
    fromGraph (toGraph s) = s := by
  ext ⟨⟨u,v⟩,h⟩
  exact (mem_fromGraph (toGraph s) ⟨(u,v),h⟩).trans (toGraph_adj_iff s h)

@[simp] theorem toGraph_fromGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    toGraph (fromGraph G) = G := by
  ext u v
  rcases lt_trichotomy u v with h | rfl | h
  · exact (toGraph_adj_iff _ h).trans (mem_fromGraph G _)
  · simp
  · constructor
    · intro huv
      exact ((mem_fromGraph G _).mp ((toGraph_adj_iff _ h).mp huv.symm)).symm
    · intro huv
      exact ((toGraph_adj_iff _ h).mpr ((mem_fromGraph G _).mpr huv.symm)).symm

def graphEquiv (n : ℕ) : Finset (Edge n) ≃ SimpleGraph (Fin n) where
  toFun := toGraph
  invFun := fromGraph
  left_inv := fromGraph_toGraph
  right_inv := toGraph_fromGraph

theorem proper_iff_colorable {n k : ℕ} (s : Finset (Edge n)) :
    Proper s k ↔ (toGraph s).Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c, ?_⟩⟩
    intro u v huv
    change c u ≠ c v
    rcases huv with ⟨h, he⟩ | ⟨h, he⟩
    · exact hc ⟨(u,v),h⟩ he
    · exact (hc ⟨(v,u),h⟩ he).symm
  · rintro ⟨c⟩
    refine ⟨c, ?_⟩
    intro e he
    exact c.valid ((toGraph_adj_iff s e.property).mpr he)

theorem coProper_iff_all_pairs {n k : ℕ} (s : Finset (Edge n)) :
    CoProper s k ↔ ∃ (c : Fin n → Fin k) (t : Fin k → Bool),
      ∀ u v, u ≠ v → c u = c v →
        ((toGraph s).Adj u v ↔ t (c u) = true) := by
  constructor
  · rintro ⟨c,t,ht⟩
    refine ⟨c,t,?_⟩
    intro u v hne heq
    rcases lt_or_gt_of_ne hne with h | h
    · rw [toGraph_adj_iff s h]
      exact ht ⟨(u,v),h⟩ heq
    · rw [SimpleGraph.adj_comm, toGraph_adj_iff s h, heq]
      exact ht ⟨(v,u),h⟩ heq.symm
  · rintro ⟨c,t,ht⟩
    refine ⟨c,t,?_⟩
    rintro ⟨⟨u,v⟩,h⟩ heq
    exact (toGraph_adj_iff s h).symm.trans (ht u v (ne_of_lt h) heq)

theorem coProper_iff_coColorable {n k : ℕ} (s : Finset (Edge n)) :
    CoProper s k ↔ Erdos625.CoColorable (toGraph s) k := by
  rw [coProper_iff_all_pairs]
  constructor
  · rintro ⟨c,t,ht⟩
    refine ⟨{
      color := c
      kind := fun i => if t i then .clique else .independent
      valid := ?_ }⟩
    intro i
    cases hi : t i with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        intro u hu v hv hne hadj
        change c u = i at hu
        change c v = i at hv
        have h := (ht u v hne (hu.trans hv.symm)).mp hadj
        simp [hu,hi] at h
    | true =>
        simp only [if_true]
        intro u hu v hv hne
        change c u = i at hu
        change c v = i at hv
        apply (ht u v hne (hu.trans hv.symm)).mpr
        simpa [hu] using hi
  · rintro ⟨C⟩
    refine ⟨C.color, fun i => match C.kind i with
      | .clique => true | .independent => false, ?_⟩
    intro u v hne heq
    cases hi : C.kind (C.color u) with
    | independent =>
        simp only [hi, Bool.false_eq_true, iff_false]
        exact C.valid_independent hi rfl heq.symm hne
    | clique =>
        simp only [hi, iff_true]
        exact C.valid_clique hi rfl heq.symm hne

theorem chi_eq_chromaticNumberNat {n : ℕ} (s : Finset (Edge n)) :
    chi s = Erdos625.chromaticNumberNat (toGraph s) := by
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((proper_iff_colorable s).mpr
      (Erdos625.colorable_chromaticNumberNat _))
  · have h := ((proper_iff_colorable s).mp (chi_spec s)).chromaticNumber_le
    exact ENat.toNat_le_toNat h (by simp)

theorem zeta_eq_cochromaticNumber {n : ℕ} (s : Finset (Edge n)) :
    zeta s = Erdos625.cochromaticNumber (toGraph s) := by
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((coProper_iff_coColorable s).mpr
      (Erdos625.coColorable_cochromaticNumber _))
  · exact Erdos625.cochromaticNumber_le_of_coColorable _
      ((coProper_iff_coColorable s).mp (zeta_spec s))

theorem gap_cast_eq {n : ℕ} (s : Finset (Edge n)) :
    ((chi s - zeta s : ℕ) : ℝ) =
      (Erdos625.chromaticNumberNat (toGraph s) : ℝ) -
      (Erdos625.cochromaticNumber (toGraph s) : ℝ) := by
  rw [Nat.cast_sub (zeta_le_chi s), chi_eq_chromaticNumberNat,
    zeta_eq_cochromaticNumber]

theorem card_graph_space (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ Fintype.card (Edge n) := by
  rw [← Fintype.card_congr (graphEquiv n), Fintype.card_finset]

theorem card_event_eq_graph_event (n : ℕ) (p : SimpleGraph (Fin n) → Prop) :
    (event fun s : Finset (Edge n) => p (toGraph s)).card =
      (univ.filter p).card := by
  classical
  apply card_bij (fun s _ => toGraph s)
  · intro s hs
    simpa using hs
  · intro s _ t _ h
    exact (graphEquiv n).injective h
  · intro G hG
    refine ⟨fromGraph G, ?_, toGraph_fromGraph G⟩
    simpa using hG

/-- Exact identity between our rational counting probability and the
standard `G(n,1/2)` probability; no limiting approximation is used. -/
theorem mass_event_eq_randomGraph (n : ℕ) (p : SimpleGraph (Fin n) → Prop) :
    (mass (event fun s : Finset (Edge n) => p (toGraph s)) : ℝ) =
      (Erdos625.randomGraphMeasure n {G | p G}).toReal := by
  classical
  have hs : {G | p G} = (↑(univ.filter p) : Set (SimpleGraph (Fin n))) := by
    ext G; simp
  rw [Erdos625.randomGraphMeasure_eq_uniformOn_univ, uniformOn_univ, hs,
    Measure.count_apply_finset]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, card_graph_space,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  simp only [mass, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat,
    card_event_eq_graph_event]

theorem mass_le_one {n : ℕ} (A : Finset (Finset (Edge n))) : mass A ≤ 1 := by
  simpa only [mass_univ] using (mass_mono (subset_univ A))

end
end JSP000506
