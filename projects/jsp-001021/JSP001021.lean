import ErdosProblems.Erdos1216
import FiniteChecks

/-!
Complete tournament-disproof integration for JSP-001021.
Our contribution under GitHub account ketianzhang1-lang, with OpenAI assistance,
is the explicit restriction map, transport to all orders at least fourteen,
the fifteen-vertex endpoint and its direct contradiction of the proposed formula.
The imported fourteen-vertex proof retains Reid--Parker's mathematical credit
and the upstream Codex / GPT-5.6 Sol formalization attribution.
-/

namespace JSP001021
open Erdos1216 Function
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Encode the restriction to fourteen chosen vertices, preserving orientation. -/
def restrict14 {n : ℕ} (T : Tournament n) (e : Fin 14 ↪ Fin n) : Tournament 14 :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin (14 * 14) =>
    T.arc (e ⟨k.val / 14, by omega⟩) (e ⟨k.val % 14, by omega⟩)))).cast (List.length_ofFn)

lemma restrict14_get {n : ℕ} (T : Tournament n) (e : Fin 14 ↪ Fin n)
    (i j : Fin 14) :
    (restrict14 T e).getLsbD (i.val * 14 + j.val) = T.arc (e i) (e j) := by
  have hidx : i.val * 14 + j.val < 14 * 14 := by omega
  simp only [restrict14, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD, List.getElem?_ofFn, dite_eq_left hidx, Option.getD_some]
  congr 2
  · apply Fin.ext
    simp
    omega
  · apply Fin.ext
    simp

lemma restrict14_arc {n : ℕ} (T : Tournament n) (e : Fin 14 ↪ Fin n)
    (i j : Fin 14) : (restrict14 T e).arc i j = T.arc (e i) (e j) := by
  by_cases hij : i = j
  · subst j
    simp [Tournament.arc_self]
  have he : e i ≠ e j := fun h => hij (e.injective h)
  rcases lt_trichotomy i j with h | h | h
  · simp only [Tournament.arc, hij, ite_false, h, ite_true]
    exact restrict14_get T e i j
  · exact (hij h).elim
  · have hnot : ¬ i < j := not_lt_of_ge h.le
    rw [Tournament.arc]
    simp only [hij, ite_false, hnot]
    rw [restrict14_get]
    exact (T.arc_reverse he).symm

/-- The result holds for every tournament of every order n >= 14. -/
theorem all_orders {n : ℕ} (hn : 14 ≤ n) (T : Tournament n) :
    HasTransitiveTournament T 5 := by
  let e : Fin 14 ↪ Fin n := Fin.castLEEmb hn
  obtain ⟨v, hv, harc⟩ := directed_ramsey_five_fourteen.2 (restrict14 T e)
  refine ⟨e ∘ v, e.injective.comp hv, ?_⟩
  intro i j hij
  have h := harc i j hij
  simpa only [restrict14_arc, Function.comp_apply] using h

theorem fifteen_vertices (T : Tournament 15) : HasTransitiveTournament T 5 :=
  all_orders (by omega) T

theorem guaranteed_fifteen : Guaranteed 15 5 :=
  ⟨by omega, fifteen_vertices⟩

theorem five_le_f_fifteen : 5 ≤ f 15 :=
  Nat.le_findGreatest (by omega) guaranteed_fifteen

/-- A complete negation of the proposed universal equality, at n = 15. -/
theorem jsp_001021 : ¬ (∀ n, 1 ≤ n → f n = Nat.log2 n + 1) := by
  intro h
  have h15 := h 15 (by omega)
  have hlog : Nat.log2 15 + 1 = 4 := by decide
  have hlo := five_le_f_fifteen
  rw [h15, hlog] at hlo
  omega

end
end JSP001021
