import JSP001021

namespace Verify1021
open Erdos1216

/-- Independent encoding of an arbitrary Boolean relation on fifteen vertices. -/
def encode15 (R : Fin 15 → Fin 15 → Bool) : Tournament 15 :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin (15 * 15) =>
    R ⟨k.val / 15, by omega⟩ ⟨k.val % 15, by omega⟩))).cast List.length_ofFn

theorem encode15_get (R : Fin 15 → Fin 15 → Bool) (i j : Fin 15) :
    (encode15 R).getLsbD (i.val * 15 + j.val) = R i j := by
  have hidx : i.val * 15 + j.val < 15 * 15 := by omega
  simp only [encode15, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD, List.getElem?_ofFn, dite_eq_left hidx, Option.getD_some]
  congr 2 <;> omega

/-- No tournament is lost by the bit-vector representation. -/
theorem encode15_arc (R : Fin 15 → Fin 15 → Bool)
    (hloop : ∀ i, R i i = false)
    (hreverse : ∀ i j, i ≠ j → R i j = !R j i) (i j : Fin 15) :
    (encode15 R).arc i j = R i j := by
  by_cases hij : i = j
  · subst j
    rw [Tournament.arc_self, hloop]
  rcases lt_trichotomy i j with h | h | h
  · simp only [Tournament.arc, hij, ite_false, h, ite_true]
    exact encode15_get R i j
  · exact (hij h).elim
  · have hnot : ¬ i < j := not_lt_of_ge h.le
    rw [Tournament.arc]
    simp only [hij, ite_false, hnot]
    rw [encode15_get]
    exact (hreverse i j hij).symm

/-- Every actual tournament relation on fifteen vertices has an ordered transitive five-set. -/
theorem fifteen_all_relations (R : Fin 15 → Fin 15 → Bool)
    (hloop : ∀ i, R i i = false)
    (hreverse : ∀ i j, i ≠ j → R i j = !R j i) :
    ∃ v : Fin 5 → Fin 15, Function.Injective v ∧
      ∀ i j : Fin 5, i < j → R (v i) (v j) = true := by
  obtain ⟨v, hv, harc⟩ := JSP001021.fifteen_vertices (encode15 R)
  refine ⟨v, hv, ?_⟩
  intro i j hij
  have h := harc i j hij
  rw [encode15_arc R hloop hreverse] at h
  exact h

-- Classical decidability is used for the literal universal predicate.
-- Equality of the two maxima is proved extensionally below, without requiring
-- their synthesized DecidablePred instances to reduce definitionally alike.
attribute [local instance] Classical.propDecidable

/-- The extremal function is the largest universally guaranteed transitive order, bounded by n. -/
noncomputable def extremal (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k ≤ n ∧ ∀ T : Tournament n,
    ∃ v : Fin k → Fin n, Function.Injective v ∧
      ∀ i j : Fin k, i < j → T.arc (v i) (v j) = true) n

theorem literal_extremal (n : ℕ) : extremal n = Erdos1216.f n := by
  unfold extremal Erdos1216.f
  apply Nat.le_antisymm
  · refine Nat.findGreatest_mono_left ?_ n
    intro k hk
    exact ⟨hk.1, fun T => hk.2 T⟩
  · refine Nat.findGreatest_mono_left ?_ n
    intro k hk
    exact ⟨hk.1, fun T => hk.2 T⟩

/-- The historical n=15 question has a strict negative answer. No exact value at 15 is asserted. -/
theorem counterexample_at_fifteen : Nat.log2 15 + 1 < extremal 15 := by
  rw [literal_extremal]
  have h := JSP001021.five_le_f_fifteen
  have hl : Nat.log2 15 + 1 = 4 := by decide
  rw [hl]
  omega

/-- Complete negation of the universal formula, with the extremal definition exposed above. -/
theorem intended : ¬ (∀ n : ℕ, 1 ≤ n → extremal n = Nat.log2 n + 1) := by
  intro h
  have h15 := h 15 (by omega)
  have hc := counterexample_at_fifteen
  rw [h15] at hc
  exact (lt_irrefl _ hc)

end Verify1021
