import Multicolor

open scoped BigOperators
namespace Verify438Color

theorem intended {C : Type} [Fintype C] [Nonempty C]
    (m : C → ℕ) (hm : ∀ c, 2 ≤ m c)
    (T : (c : C) → SimpleGraph (Fin (m c))) (ht : ∀ c, (T c).IsTree)
    (χ : Sym2 (Fin ((∑ c, (m c - 2)) + 2)) → C) :
    ∃ c, ∃ f : Fin (m c) ↪ Fin ((∑ c, (m c - 2)) + 2),
      ∀ a b, (T c).Adj a b → χ s(f a, f b) = c :=
  JSP000438.multicolor_tree_embedding m hm T ht χ

end Verify438Color
