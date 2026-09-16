import JSP000617

/-!
Finite translate covering for the upper-density construction.
This is a finite-scale development, NOT the infinite-natural-number theorem.
The greedy averaging argument is classical; no discovery or prize claim is made.
-/
namespace JSP000617

section Cover
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Translation defined by ordinary group subtraction. -/
def translateSet (S : Finset G) (t : G) : Finset G :=
  Finset.univ.filter (fun u => u - t ∈ S)

def translateCover (S T : Finset G) : Finset G :=
  T.biUnion (translateSet S)

def uncovered (S T : Finset G) : Finset G :=
  Finset.univ \ translateCover S T

/-- Exact double counting of uncovered points under all translations. -/
lemma sum_misses (S U : Finset G) :
    ∑ t : G, (U.filter (fun u => u - t ∉ S)).card =
      U.card * (Fintype.card G - S.card) := by
  classical
  have hcard (u : G) :
      ((Finset.univ : Finset G).filter (fun t => u - t ∉ S)).card =
        ((Finset.univ : Finset G) \ S).card := by
    apply Finset.card_bij (fun t _ => u - t)
    · intro t ht
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
    · intro t _ht v _hv heq
      exact sub_right_injective heq
    · intro b hb
      refine ⟨u - b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using (Finset.mem_sdiff.mp hb).2
      · simp
  calc
    ∑ t : G, (U.filter (fun u => u - t ∉ S)).card =
        ∑ t : G, ∑ u ∈ U, if u - t ∉ S then 1 else 0 := by simp
    _ = ∑ u ∈ U, ∑ t : G, if u - t ∉ S then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ _u ∈ U, ((Finset.univ : Finset G) \ S).card := by
      apply Finset.sum_congr rfl
      intro u _hu
      simpa only [Finset.sum_boole] using hcard u
    _ = U.card * (Fintype.card G - S.card) := by simp

/-- Some translation misses no more than the average number of points. -/
lemma exists_small_miss (S U : Finset G) :
    ∃ t : G, (U.filter (fun u => u - t ∉ S)).card * Fintype.card G ≤
      U.card * (Fintype.card G - S.card) := by
  classical
  by_contra h
  push_neg at h
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := G))
    (fun t _ht => h t)
  have hsum := sum_misses S U
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.sum_mul] at hlt
  rw [hsum] at hlt
  nlinarith

/-- A half-dense set can cover at least half of any specified remaining set. -/
lemma exists_halving_translate (S U : Finset G)
    (hhalf : Fintype.card G ≤ 2 * S.card) :
    ∃ t : G, 2 * (U.filter (fun u => u - t ∉ S)).card ≤ U.card := by
  obtain ⟨t, ht⟩ := exists_small_miss S U
  have hc : S.card ≤ Fintype.card G := Finset.card_le_univ S
  have hcomp : 2 * (Fintype.card G - S.card) ≤ Fintype.card G := by omega
  refine ⟨t, Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := G))⟩
  calc
    (2 * (U.filter (fun u => u - t ∉ S)).card) * Fintype.card G =
        2 * ((U.filter (fun u => u - t ∉ S)).card * Fintype.card G) := by ring
    _ ≤ 2 * (U.card * (Fintype.card G - S.card)) := Nat.mul_le_mul_left 2 ht
    _ = U.card * (2 * (Fintype.card G - S.card)) := by ring
    _ ≤ U.card * Fintype.card G := Nat.mul_le_mul_left U.card hcomp

lemma uncovered_insert (S T : Finset G) (t : G) :
    uncovered S (insert t T) = (uncovered S T).filter (fun u => u - t ∉ S) := by
  classical
  ext u
  simp only [uncovered, translateCover, translateSet, Finset.biUnion_insert,
    Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_filter, not_or]
  tauto

/-- After at most m translations, at most a 2^(-m) fraction is uncovered.
All cardinalities refer to the actual finite group, not a density surrogate. -/
theorem exists_small_uncovered (S : Finset G)
    (hhalf : Fintype.card G ≤ 2 * S.card) (m : ℕ) :
    ∃ T : Finset G, T.card ≤ m ∧ (uncovered S T).card * 2 ^ m ≤ Fintype.card G := by
  classical
  induction m with
  | zero =>
    exact ⟨∅, by simp, by simp [uncovered, translateCover]⟩
  | succ m ih =>
    obtain ⟨T, hT, hmiss⟩ := ih
    obtain ⟨t, ht⟩ := exists_halving_translate S (uncovered S T) hhalf
    refine ⟨insert t T, (Finset.card_insert_le t T).trans (by omega), ?_⟩
    rw [uncovered_insert, pow_succ]
    calc
      ((uncovered S T).filter (fun u => u - t ∉ S)).card * (2 ^ m * 2) =
          (2 * ((uncovered S T).filter (fun u => u - t ∉ S)).card) * 2 ^ m := by ring
      _ ≤ (uncovered S T).card * 2 ^ m := Nat.mul_le_mul_right (2 ^ m) ht
      _ ≤ Fintype.card G := hmiss

end Cover

section Plane
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ordinary finite sumset of actual points. -/
def planeSumset (A : Finset (F × F)) : Finset (F × F) :=
  (A ×ˢ A).image (fun ab => ab.1 + ab.2)

lemma translated_sums_subset (T : Finset (F × F)) :
    translateCover (parabolaSumset (F := F)) T ⊆ planeSumset (curveUnion (insert 0 T)) := by
  classical
  intro z hz
  obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz
  have hrep := (Finset.mem_filter.mp hzt).2
  obtain ⟨xy, _hxy, heq⟩ := Finset.mem_image.mp hrep
  let a : F × F := (xy.1, xy.1 ^ 2)
  let b : F × F := (xy.2, xy.2 ^ 2)
  have ha : a ∈ curveUnion (insert 0 T) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
    exact Finset.mem_image.mpr ⟨xy.1, Finset.mem_univ _, by simp [a]⟩
  have hb : b + t ∈ curveUnion (insert 0 T) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_insert_of_mem ht, ?_⟩
    exact Finset.mem_image.mpr ⟨xy.2, Finset.mem_univ _, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨(a, b + t), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
  change a + (b + t) = z
  calc
    a + (b + t) = pairSumMap xy + t := by rfl
    _ = (z - t) + t := by rw [heq]
    _ = z := sub_add_cancel z t

/-- A finite-scale near-covering family with representation bound independent
of field size. The transfer to natural numbers and infinite scales is not in this theorem. -/
theorem finite_plane_construction (htwo : (2 : F) ≠ 0) (m : ℕ) :
    ∃ A : Finset (F × F),
      ((Finset.univ : Finset (F × F)) \ planeSumset A).card * 2 ^ m ≤ Fintype.card F ^ 2 ∧
      ∀ z : F × F, (sumRepresentations A A z).card ≤ 2 * (m + 1) ^ 2 := by
  classical
  have hh : Fintype.card (F × F) ≤ 2 * (parabolaSumset (F := F)).card := by
    simpa [pow_two] using parabolaSumset_large htwo
  obtain ⟨T, hT, hmiss⟩ := exists_small_uncovered (parabolaSumset (F := F)) hh m
  refine ⟨curveUnion (insert 0 T), ?_, ?_⟩
  · have hsub : ((Finset.univ : Finset (F × F)) \ planeSumset (curveUnion (insert 0 T))) ⊆
        uncovered (parabolaSumset (F := F)) T := by
      intro z hz
      obtain ⟨hzuniv, hznot⟩ := Finset.mem_sdiff.mp hz
      exact Finset.mem_sdiff.mpr ⟨hzuniv, fun h => hznot (translated_sums_subset T h)⟩
    have hle := (Nat.mul_le_mul_right (2 ^ m) (Finset.card_le_card hsub)).trans hmiss
    simpa [pow_two] using hle
  · intro z
    have hcard : (insert (0 : F × F) T).card ≤ m + 1 :=
      (Finset.card_insert_le _ T).trans (by omega)
    have hsq := Nat.mul_self_le_mul_self hcard
    exact (curveUnion_representations_le htwo (insert 0 T) z).trans
      (by simpa [pow_two] using Nat.mul_le_mul_left 2 hsq)

end Plane
end JSP000617
