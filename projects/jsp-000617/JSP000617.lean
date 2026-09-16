import Mathlib

/-!
# JSP-000617 / Erdos 749: finite-field building blocks

WORK IN PROGRESS: this file does not prove the upper-density theorem, and is not
an award submission. These classical parabola facts support the construction
outlined by Bhalla and Tao. No mathematical discovery or priority is claimed.
Prepared with OpenAI ChatGPT assistance under the repository owner's direction.
-/

namespace JSP000617

section Algebra
variable {F : Type*} [Field F]

/-- In characteristic different from two, sum and sum of squares determine
an unordered pair. This controls ordered representations on a parabola. -/
theorem sum_sq_collision (htwo : (2 : F) != 0) {x y u v : F}
    (hsum : x + y = u + v) (hsq : x ^ 2 + y ^ 2 = u ^ 2 + v ^ 2) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hy : y = u + v - x := by linear_combination hsum
  have he : (2 : F) * ((x - u) * (x - v)) = 0 := by
    rw [hy] at hsq
    linear_combination hsq
  have hz : (x - u) * (x - v) = 0 := (mul_eq_zero.mp he).resolve_left htwo
  rcases mul_eq_zero.mp hz with hxu | hxv
  · exact Or.inl ⟨sub_eq_zero.mp hxu, by linear_combination hsum - hxu⟩
  · exact Or.inr ⟨sub_eq_zero.mp hxv, by linear_combination hsum - hxv⟩

end Algebra

section FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Ordered parameter pairs representing (s,t) as a sum of parabola points. -/
def pairSumFiber (s t : F) : Finset (F × F) :=
  Finset.univ.filter (fun xy => xy.1 + xy.2 = s ∧ xy.1 ^ 2 + xy.2 ^ 2 = t)

/-- The actual two-dimensional sum map, not a surrogate Boolean predicate. -/
def pairSumMap (xy : F × F) : F × F :=
  (xy.1 + xy.2, xy.1 ^ 2 + xy.2 ^ 2)

def parabolaSumset : Finset (F × F) := Finset.univ.image pairSumMap

/-- Every point has at most two ordered parabola representations. -/
theorem pairSumFiber_card_le_two (htwo : (2 : F) != 0) (s t : F) :
    (pairSumFiber s t).card ≤ 2 := by
  classical
  by_cases he : (pairSumFiber s t).Nonempty
  · obtain ⟨⟨u, v⟩, huv⟩ := he
    have hu := (Finset.mem_filter.mp huv).2
    have hsub : pairSumFiber s t ⊆ ({(u, v), (v, u)} : Finset (F × F)) := by
      intro xy hxy
      have hx := (Finset.mem_filter.mp hxy).2
      rcases sum_sq_collision htwo (hx.1.trans hu.1.symm) (hx.2.trans hu.2.symm) with h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        exact Or.inl (Prod.ext h.1 h.2)
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        exact Or.inr (Prod.ext h.1 h.2)
    calc
      (pairSumFiber s t).card ≤ ({(u, v), (v, u)} : Finset (F × F)).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := by
        have h := Finset.card_insert_le (u, v) ({(v, u)} : Finset (F × F))
        simpa using h
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

/-- At least half of the finite plane is covered by the parabola sumset.
This is only a finite-scale lemma, not an infinite density conclusion. -/
theorem parabolaSumset_large (htwo : (2 : F) != 0) :
    Fintype.card F ^ 2 ≤ 2 * (parabolaSumset (F := F)).card := by
  classical
  have hcover : (Finset.univ : Finset (F × F)) ⊆
      (parabolaSumset (F := F)).biUnion (fun z => pairSumFiber z.1 z.2) := by
    intro xy hxy
    apply Finset.mem_biUnion.mpr
    refine ⟨pairSumMap xy, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨xy, hxy, rfl⟩
    · simp [pairSumFiber, pairSumMap]
  calc
    Fintype.card F ^ 2 = (Finset.univ : Finset (F × F)).card := by simp [pow_two]
    _ ≤ ((parabolaSumset (F := F)).biUnion (fun z => pairSumFiber z.1 z.2)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ z ∈ (parabolaSumset (F := F)), (pairSumFiber z.1 z.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ (parabolaSumset (F := F)), 2 :=
      Finset.sum_le_sum (fun z _hz => pairSumFiber_card_le_two htwo z.1 z.2)
    _ = 2 * (parabolaSumset (F := F)).card := by simp [Nat.mul_comm]

end FiniteField
end JSP000617
