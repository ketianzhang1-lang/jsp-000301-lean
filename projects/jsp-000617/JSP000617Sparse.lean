import JSP000617Cover

/-!
Horizontal sparsity for the finite-plane building block. The final infinite
natural-number construction is not proved by this file.
-/
namespace JSP000617
section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def squareFiber (t : F) : Finset F :=
  Finset.univ.filter (fun x => x ^ 2 = t)

lemma squareFiber_card_le_two (t : F) : (squareFiber t).card ≤ 2 := by
  classical
  by_cases he : (squareFiber t).Nonempty
  · obtain ⟨u, hu⟩ := he
    have hu2 := (Finset.mem_filter.mp hu).2
    have hsub : squareFiber t ⊆ ({u, -u} : Finset F) := by
      intro x hx
      have hx2 := (Finset.mem_filter.mp hx).2
      have hz : (x - u) * (x + u) = 0 := by linear_combination hx2 - hu2
      rcases mul_eq_zero.mp hz with h | h
      · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp h))
      · apply Finset.mem_insert.mpr
        exact Or.inr (Finset.mem_singleton.mpr (by linear_combination h))
    calc
      (squareFiber t).card ≤ ({u, -u} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 2 := by simpa using Finset.card_insert_le u ({-u} : Finset F)
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

def rowPoints (A : Finset (F × F)) (y : F) : Finset (F × F) :=
  A.filter (fun z => z.2 = y)

lemma translated_row_card_le_two (c : F × F) (y : F) :
    (rowPoints (translatedParabola c) y).card ≤ 2 := by
  classical
  have hsub : rowPoints (translatedParabola c) y ⊆
      (squareFiber (y - c.2)).image (fun x => (x, x ^ 2) + c) := by
    intro z hz
    obtain ⟨hzc, hzy⟩ := Finset.mem_filter.mp hz
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hzc
    change x ^ 2 + c.2 = y at hzy
    refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linear_combination hzy⟩
  calc
    (rowPoints (translatedParabola c) y).card ≤
        ((squareFiber (y - c.2)).image (fun x => (x, x ^ 2) + c)).card :=
      Finset.card_le_card hsub
    _ ≤ (squareFiber (y - c.2)).card := Finset.card_image_le
    _ ≤ 2 := squareFiber_card_le_two _

theorem curveUnion_row_card_le (T : Finset (F × F)) (y : F) :
    (rowPoints (curveUnion T) y).card ≤ 2 * T.card := by
  classical
  have hsub : rowPoints (curveUnion T) y ⊆
      T.biUnion (fun c => rowPoints (translatedParabola c) y) := by
    intro z hz
    obtain ⟨hzT, hzy⟩ := Finset.mem_filter.mp hz
    obtain ⟨c, hc, hzc⟩ := Finset.mem_biUnion.mp hzT
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hzc, hzy⟩⟩
  calc
    (rowPoints (curveUnion T) y).card ≤
        (T.biUnion (fun c => rowPoints (translatedParabola c) y)).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ T, (rowPoints (translatedParabola c) y).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ T, 2 := Finset.sum_le_sum (fun c _hc => translated_row_card_le_two c y)
    _ = 2 * T.card := by simp [Nat.mul_comm]

/-- The complete finite-plane building block: near-full sumset coverage,
uniform representation bounds, and bounded intersection with every horizontal line.
It is not the transfer to the integers or the infinite-scale conclusion. -/
theorem finite_plane_construction_sparse (htwo : (2 : F) ≠ 0) (m : ℕ) :
    ∃ A : Finset (F × F),
      ((Finset.univ : Finset (F × F)) \ planeSumset A).card * 2 ^ m ≤ Fintype.card F ^ 2 ∧
      (∀ z : F × F, (sumRepresentations A A z).card ≤ 2 * (m + 1) ^ 2) ∧
      ∀ y : F, (rowPoints A y).card ≤ 2 * (m + 1) := by
  classical
  have hh : Fintype.card (F × F) ≤ 2 * (parabolaSumset (F := F)).card := by
    simpa [pow_two] using parabolaSumset_large htwo
  obtain ⟨T, hT, hmiss⟩ := exists_small_uncovered (parabolaSumset (F := F)) hh m
  have hcard : (insert (0 : F × F) T).card ≤ m + 1 :=
    (Finset.card_insert_le _ T).trans (by omega)
  refine ⟨curveUnion (insert 0 T), ?_, ?_, ?_⟩
  · have hsub : ((Finset.univ : Finset (F × F)) \ planeSumset (curveUnion (insert 0 T))) ⊆
        uncovered (parabolaSumset (F := F)) T := by
      intro z hz
      obtain ⟨hzuniv, hznot⟩ := Finset.mem_sdiff.mp hz
      exact Finset.mem_sdiff.mpr ⟨hzuniv, fun h => hznot (translated_sums_subset T h)⟩
    have hle := (Nat.mul_le_mul_right (2 ^ m) (Finset.card_le_card hsub)).trans hmiss
    simpa [pow_two] using hle
  · intro z
    have hsq := Nat.mul_self_le_mul_self hcard
    exact (curveUnion_representations_le htwo (insert 0 T) z).trans
      (by simpa [pow_two] using Nat.mul_le_mul_left 2 hsq)
  · intro y
    exact (curveUnion_row_card_le (insert 0 T) y).trans (Nat.mul_le_mul_left 2 hcard)

end
end JSP000617
