import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# A finite counting version of the random covering argument

All choices are over finite types. No probabilistic oracle or numerical certificate
is assumed. The argument counts tuples that fail at least one requirement.
-/
namespace JSP000749
open Finset
open scoped Classical

/-- If the union bound is strictly smaller than the entire tuple space, some
length-M tuple meets every requirement. -/
theorem exists_hitting_tuple {α β : Type*} [Fintype α] [Fintype β]
    (R : β → α → Prop) (M D : ℕ)
    (hD : ∀ b, D ≤ Fintype.card {a : α // R b a})
    (hbound : Fintype.card β * (Fintype.card α - D) ^ M < (Fintype.card α) ^ M) :
    ∃ f : Fin M → α, ∀ b, ∃ i, R b (f i) := by
  classical
  by_contra! h
  choose bad hbad using h
  let enc : (Fin M → α) → Σ b : β, (Fin M → {a : α // ¬ R b a}) :=
    fun f => ⟨bad f, fun i => ⟨f i, hbad f i⟩⟩
  have hi : Function.Injective enc := by
    intro f g hfg
    exact congrArg (fun s : Σ b : β, (Fin M → {a : α // ¬ R b a}) =>
      fun i => (s.2 i).1) hfg
  have hcount := Fintype.card_le_of_injective enc hi
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_sigma] at hcount
  have hle : (∑ b : β, (Fintype.card {a : α // ¬ R b a}) ^ M) ≤
      Fintype.card β * (Fintype.card α - D) ^ M := by
    calc
      _ ≤ ∑ _b : β, (Fintype.card α - D) ^ M := by
        apply Finset.sum_le_sum
        intro b _
        apply Nat.pow_le_pow_left
        rw [Fintype.card_subtype_compl]
        exact Nat.sub_le_sub_left (hD b) _
      _ = _ := by simp
  exact (not_lt_of_ge (hcount.trans hle)) hbound

end JSP000749
