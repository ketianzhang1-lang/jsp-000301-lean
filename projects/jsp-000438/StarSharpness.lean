/-
Copyright 2026 Ketian Zhang. Licensed under Apache-2.0.
Prepared with OpenAI ChatGPT assistance.
Classical sharpness examples for the tree Ramsey upper bound.
-/
import JSP000438
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.ZMod.Basic

namespace JSP000438
open SimpleGraph

/-- The cyclic graph on `4*k+1` vertices with jumps of size at most `k`.
Both this graph and its complement have degree `2*k` at every vertex. -/
def sharpGraph (k : ℕ) : SimpleGraph (ZMod (4 * k + 1)) where
  Adj a b := a ≠ b ∧ ((b - a).val ≤ k ∨ 3 * k < (b - a).val)
  symm := ⟨by
    intro a b h
    have hne : b - a ≠ 0 := sub_ne_zero.mpr h.1.symm
    have hv := ZMod.val_lt (b - a)
    have hp := ZMod.val_pos.mpr hne
    have he : (a - b).val = 4 * k + 1 - (b - a).val := by
      rw [← neg_sub, ZMod.neg_val, ite_eq_right hne]
    exact ⟨h.1.symm, by rw [he]; omega⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance (k : ℕ) : DecidableRel (sharpGraph k).Adj :=
  fun a b => inferInstanceAs (Decidable
    (a ≠ b ∧ ((b - a).val ≤ k ∨ 3 * k < (b - a).val)))

lemma sharpGraph_degree_le (k : ℕ) (a : ZMod (4 * k + 1)) :
    (sharpGraph k).degree a ≤ 2 * k := by
  classical
  let f : (sharpGraph k).neighborSet a → Fin (2 * k) := fun b =>
    ⟨if (b.val - a).val ≤ k then (b.val - a).val - 1
      else (b.val - a).val - 2 * k - 1, by
      have hb : a ≠ b.val ∧ ((b.val - a).val ≤ k ∨ 3 * k < (b.val - a).val) := b.prop
      have hp := ZMod.val_pos.mpr (sub_ne_zero.mpr hb.1.symm)
      have hv := ZMod.val_lt (b.val - a)
      split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro b c h
    have hb : a ≠ b.val ∧ ((b.val - a).val ≤ k ∨ 3 * k < (b.val - a).val) := b.prop
    have hc : a ≠ c.val ∧ ((c.val - a).val ≤ k ∨ 3 * k < (c.val - a).val) := c.prop
    have hbp := ZMod.val_pos.mpr (sub_ne_zero.mpr hb.1.symm)
    have hcp := ZMod.val_pos.mpr (sub_ne_zero.mpr hc.1.symm)
    have hbv := ZMod.val_lt (b.val - a)
    have hcv := ZMod.val_lt (c.val - a)
    have he := congrArg Fin.val h
    change (if (b.val - a).val ≤ k then (b.val - a).val - 1
      else (b.val - a).val - 2 * k - 1) =
      (if (c.val - a).val ≤ k then (c.val - a).val - 1
      else (c.val - a).val - 2 * k - 1) at he
    have hv : (b.val - a).val = (c.val - a).val := by
      split_ifs at he <;> omega
    apply Subtype.ext
    exact sub_left_injective (ZMod.val_injective (4 * k + 1) hv)
  simpa only [Fintype.card_fin, card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

lemma sharpGraph_compl_degree_le (k : ℕ) (a : ZMod (4 * k + 1)) :
    (sharpGraph k)ᶜ.degree a ≤ 2 * k := by
  classical
  have hbnd : ∀ b : (sharpGraph k)ᶜ.neighborSet a,
      k < (b.val - a).val ∧ (b.val - a).val ≤ 3 * k := by
    intro b
    obtain ⟨hne, hb⟩ := (compl_adj (sharpGraph k) a b.val).mp b.prop
    change ¬(a ≠ b.val ∧ ((b.val - a).val ≤ k ∨ 3 * k < (b.val - a).val)) at hb
    have hn : ¬((b.val - a).val ≤ k ∨ 3 * k < (b.val - a).val) :=
      fun h => hb ⟨hne, h⟩
    omega
  let f : (sharpGraph k)ᶜ.neighborSet a → Fin (2 * k) := fun b =>
    ⟨(b.val - a).val - k - 1, by have := hbnd b; omega⟩
  have hf : Function.Injective f := by
    intro b c h
    have hb := hbnd b
    have hc := hbnd c
    have he := congrArg Fin.val h
    change (b.val - a).val - k - 1 = (c.val - a).val - k - 1 at he
    have hv : (b.val - a).val = (c.val - a).val := by omega
    apply Subtype.ext
    exact sub_left_injective (ZMod.val_injective (4 * k + 1) hv)
  simpa only [Fintype.card_fin, card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

/-- The explicit coloring on `4*k+1` vertices has no star with `2*k+1` leaves
in either color. This includes `k=0`. -/
theorem sharpGraph_avoids_star (k : ℕ) :
    let T := starGraph (0 : Fin (2 * k + 2))
    ¬T.IsContained (sharpGraph k) ∧ ¬T.IsContained (sharpGraph k)ᶜ := by
  classical
  constructor
  · rintro ⟨f⟩
    have h := f.degree_le 0
    have hb := sharpGraph_degree_le k (f 0)
    rw [degree_starGraph_center, Fintype.card_fin] at h
    omega
  · rintro ⟨f⟩
    have h := f.degree_le 0
    have hb := sharpGraph_compl_degree_le k (f 0)
    rw [degree_starGraph_center, Fintype.card_fin] at h
    omega

/-- A finite counterexample bounds the actual Ramsey infimum from below;
nonemptiness of the Ramsey set is an explicit premise. -/
lemma card_lt_graphRamsey_of_counterexample {U V : Type*} [Fintype U] [Fintype V]
    (T : SimpleGraph U) (G : SimpleGraph V)
    (hG : ¬T.IsContained G) (hGc : ¬T.IsContained Gᶜ)
    (hne : {n : ℕ | ∀ C : SimpleGraph (Fin n),
      T.IsContained C ∨ T.IsContained Cᶜ}.Nonempty) :
    Fintype.card V < SimpleGraph.diagonalGraphRamsey T := by
  classical
  by_contra h
  have hcard : Fintype.card (Fin (SimpleGraph.diagonalGraphRamsey T)) ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using (not_lt.mp h)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hp := Nat.sInf_mem hne
  change ∀ C : SimpleGraph (Fin (SimpleGraph.diagonalGraphRamsey T)),
    T.IsContained C ∨ T.IsContained Cᶜ at hp
  let e := SimpleGraph.Embedding.comap f G
  rcases hp (G.comap f) with h | h
  · obtain ⟨g⟩ := h
    exact hG ⟨e.toCopy.comp g⟩
  · obtain ⟨g⟩ := h
    exact hGc ⟨(SimpleGraph.Embedding.complEquiv e).toCopy.comp g⟩

/-- The bound `R(T,T) ≤ 2*n-2` is attained by every even-order star. -/
theorem star_ramsey_even_order (k : ℕ) :
    SimpleGraph.diagonalGraphRamsey (starGraph (0 : Fin (2 * k + 2))) = 4 * k + 2 := by
  have ht := isTree_starGraph (0 : Fin (2 * k + 2))
  have hu := Erdos547.erdos_547 (2 * k + 2) (by omega) _ ht
  have hne : {n : ℕ | ∀ C : SimpleGraph (Fin n),
      (starGraph (0 : Fin (2 * k + 2))).IsContained C ∨
      (starGraph (0 : Fin (2 * k + 2))).IsContained Cᶜ}.Nonempty :=
    ⟨2 * (2 * k + 2) - 2, tree_monochromatic _ (by omega) _ ht⟩
  have havoid := sharpGraph_avoids_star k
  have hl := card_lt_graphRamsey_of_counterexample _ (sharpGraph k) havoid.1 havoid.2 hne
  rw [ZMod.card] at hl
  omega

/-- A full universal upper bound together with a matching example for each
even order; no finite-range check or unproved extremal premise is used. -/
theorem tree_ramsey_bound_is_sharp :
    (∀ (n : ℕ), 2 ≤ n → ∀ T : SimpleGraph (Fin n),
      T.IsTree → SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2) ∧
    (∀ k : ℕ, ∃ T : SimpleGraph (Fin (2 * k + 2)),
      T.IsTree ∧ SimpleGraph.diagonalGraphRamsey T = 4 * k + 2) := by
  refine ⟨Erdos547.erdos_547, ?_⟩
  intro k
  exact ⟨starGraph 0, isTree_starGraph 0, star_ramsey_even_order k⟩

end JSP000438
