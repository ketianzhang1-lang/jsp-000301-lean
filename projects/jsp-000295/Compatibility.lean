/-
Statement-only extraction adapted from the Formal Conjectures Authors (2025),
licensed under Apache 2.0, commit 40e7c98697de6f66b8cbdbf641749ab39ed9c152,
FormalConjectures/ErdosProblems/357.lean. Metadata attributes are omitted;
the mathematical definitions and the target type are retained.
This file imports no admitted conjecture or upstream proof placeholder.
-/
import JSP000295

namespace Erdos357
open Filter Asymptotics

def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

theorem erdos_357.variants.weisenberg : ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (2 + o n) * √n ≤ f n :=
  JSP000295.weisenberg

theorem explicit_lower_bound (n : ℕ) : 2 * n.sqrt - 1 ≤ f n :=
  JSP000295.lower_bound n

end Erdos357
