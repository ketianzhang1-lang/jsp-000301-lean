import JSP000140
import ErdosProblems.Erdos136.Definitions

/-! We connect our symmetric pair-colouring model to genuine unordered edges.
The diagonal is ignored in admissibility but needs a palette value when n > 0.
Consequently the exact minimum comparison is stated for n >= 2. -/
namespace JSP000140
open Finset
attribute [local instance] Classical.propDecidable

abbrev topEdge {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    (⊤ : SimpleGraph (Fin n)).edgeSet := ⟨s(a,b), by simpa using h⟩

theorem four_edges : (univ : Finset (⊤ : SimpleGraph (Fin 4)).edgeSet) =
    {topEdge 0 1 (by decide), topEdge 0 2 (by decide), topEdge 0 3 (by decide),
     topEdge 1 2 (by decide), topEdge 1 3 (by decide), topEdge 2 3 (by decide)} := by
  decide

theorem pullback_topEdge {n k m : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (v : Fin m ↪ Fin n)
    (a b : Fin m) (h : a ≠ b) :
    C.pullback v (topEdge a b h) = C (topEdge (v a) (v b) (v.injective.ne h)) := rfl

theorem six_image {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (v : Fin 4 ↪ Fin n) :
    univ.image (C.pullback v) =
    {C (topEdge (v 0) (v 1) (v.injective.ne (by decide))),
     C (topEdge (v 0) (v 2) (v.injective.ne (by decide))),
     C (topEdge (v 0) (v 3) (v.injective.ne (by decide))),
     C (topEdge (v 1) (v 2) (v.injective.ne (by decide))),
     C (topEdge (v 1) (v 3) (v.injective.ne (by decide))),
     C (topEdge (v 2) (v 3) (v.injective.ne (by decide)))} := by
  change univ.image (fun e : (⊤ : SimpleGraph (Fin 4)).edgeSet => C.pullback v e) = _
  rw [four_edges]
  simp only [image_insert, image_singleton, pullback_topEdge]

def toEdges {n k : ℕ} (χ : Coloring n k) (hsym : ∀ a b, χ a b = χ b a) :
    SimpleGraph.TopEdgeLabeling (Fin n) (Fin k) :=
  SimpleGraph.EdgeLabeling.mk (fun a b _ => χ a b) (fun a b _ => hsym b a)

@[simp] theorem toEdges_apply {n k : ℕ} (χ : Coloring n k) (hsym)
    (a b : Fin n) (h : a ≠ b) : toEdges χ hsym (topEdge a b h) = χ a b := rfl

theorem toEdges_admissible {n k : ℕ} (χ : Coloring n k) (hχ : Admissible χ) :
    Erdos136.Is45Coloring (toEdges χ hχ.1) := by
  intro v
  rw [six_image]
  simpa only [toEdges_apply, Colors4] using
    hχ.2 (v 0) (v 1) (v 2) (v 3) (v.injective.ne (by decide))
      (v.injective.ne (by decide)) (v.injective.ne (by decide))
      (v.injective.ne (by decide)) (v.injective.ne (by decide))
      (v.injective.ne (by decide))

def fromEdges {n k : ℕ} (hk : 0 < k)
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Coloring n k :=
  fun a b => if h : a ≠ b then C (topEdge a b h) else ⟨0,hk⟩

@[simp] theorem fromEdges_apply {n k : ℕ} (hk : 0 < k)
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (a b : Fin n) (h : a ≠ b) :
    fromEdges hk C a b = C (topEdge a b h) := dite_eq_left h

theorem fromEdges_symm {n k : ℕ} (hk : 0 < k)
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (a b : Fin n) :
    fromEdges hk C a b = fromEdges hk C b a := by
  by_cases h : a = b
  · subst b; rfl
  · rw [fromEdges_apply hk C a b h, fromEdges_apply hk C b a (Ne.symm h)]
    congr 1
    exact Subtype.ext Sym2.eq_swap

def quadEmbedding {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Fin n where
  toFun := ![a,b,c,d]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem fromEdges_admissible {n k : ℕ} (hk : 0 < k)
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (hC : Erdos136.Is45Coloring C) :
    Admissible (fromEdges hk C) := by
  refine ⟨fromEdges_symm hk C, ?_⟩
  intro a b c d hab hac had hbc hbd hcd
  have h := hC (quadEmbedding a b c d hab hac had hbc hbd hcd)
  rw [six_image] at h
  change 5 ≤ ({C (topEdge a b hab), C (topEdge a c hac), C (topEdge a d had),
    C (topEdge b c hbc), C (topEdge b d hbd), C (topEdge c d hcd)} : Finset (Fin k)).card at h
  simpa only [Colors4, fromEdges_apply hk C a b hab, fromEdges_apply hk C a c hac,
    fromEdges_apply hk C a d had, fromEdges_apply hk C b c hbc,
    fromEdges_apply hk C b d hbd, fromEdges_apply hk C c d hcd] using h

theorem edge_palette_pos {n k : ℕ} (hn : 2 ≤ n)
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : 0 < k := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have h := (C (topEdge ⟨0,h0⟩ ⟨1,h1⟩ (by simp))).isLt
  omega

def PairColorable (n k : ℕ) : Prop := ∃ χ : Coloring n k, Admissible χ

theorem pairColorable_iff {n k : ℕ} (hn : 2 ≤ n) :
    PairColorable n k ↔ Erdos136.Colorable n k := by
  constructor
  · rintro ⟨χ,hχ⟩
    exact ⟨toEdges χ hχ.1, toEdges_admissible χ hχ⟩
  · rintro ⟨C,hC⟩
    exact ⟨fromEdges (edge_palette_pos hn C) C,
      fromEdges_admissible (edge_palette_pos hn C) C hC⟩

theorem pairColorable_nonempty (n : ℕ) : ∃ k, PairColorable n k := by
  by_cases hn : 2 ≤ n
  · obtain ⟨k,hk⟩ := Erdos136.colorable_nonempty n
    exact ⟨k,(pairColorable_iff hn).mpr hk⟩
  · refine ⟨1, (fun _ _ => 0), (fun _ _ => rfl), ?_⟩
    intro a b c d hab _ _ _ _ _
    apply (hab ?_).elim
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    omega

noncomputable def minPalette (n : ℕ) : ℕ := Nat.find (pairColorable_nonempty n)

theorem minPalette_spec (n : ℕ) : PairColorable n (minPalette n) :=
  Nat.find_spec (pairColorable_nonempty n)

theorem minPalette_le {n k : ℕ} (h : PairColorable n k) : minPalette n ≤ k :=
  Nat.find_min' (pairColorable_nonempty n) h

theorem minPalette_eq {n : ℕ} (hn : 2 ≤ n) : minPalette n = Erdos136.erdos136Fun n := by
  apply Nat.le_antisymm
  · exact minPalette_le ((pairColorable_iff hn).mpr (Erdos136.erdos136Fun_spec n))
  · exact Erdos136.erdos136Fun_min ((pairColorable_iff hn).mp (minPalette_spec n))

theorem minPalette_strict_lower {n : ℕ} (hn : 4 ≤ n) :
    5 * (n - 1) < 6 * minPalette n := by
  obtain ⟨χ,hχ⟩ := minPalette_spec n
  exact strict_lower_bound hn χ hχ

theorem minPalette_integer_lower {n : ℕ} (hn : 4 ≤ n) :
    5 * (n - 1) / 6 + 1 ≤ minPalette n := by
  obtain ⟨χ,hχ⟩ := minPalette_spec n
  exact integer_lower_bound hn χ hχ

end JSP000140
