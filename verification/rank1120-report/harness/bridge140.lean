import JSP000140Complete

/- Audit-owned definition of f(n,4,5), using genuine unordered edges and
every embedding of four vertices. No diagonal edges are included. -/
namespace Verify140
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

def Colorable (n k : ℕ) : Prop :=
  ∃ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k),
    ∀ v : Fin 4 ↪ Fin n, 5 ≤ (Finset.univ.image (C.pullback v)).card

theorem colorable_iff (n k : ℕ) :
    Colorable n k ↔ Erdos136.Colorable n k := Iff.rfl

theorem colorable_exists (n : ℕ) : ∃ k, Colorable n k :=
  Erdos136.colorable_nonempty n

noncomputable def minimum (n : ℕ) : ℕ := Nat.find (colorable_exists n)

theorem minimum_eq (n : ℕ) : minimum n = Erdos136.erdos136Fun n := rfl

theorem minimum_attained (n : ℕ) : Colorable n (minimum n) :=
  Nat.find_spec (colorable_exists n)

theorem minimum_le {n k : ℕ} (h : Colorable n k) : minimum n ≤ k :=
  Nat.find_min' (colorable_exists n) h

theorem pair_minimum_eq {n : ℕ} (hn : 2 ≤ n) :
    JSP000140.minPalette n = minimum n :=
  JSP000140.minPalette_eq hn

theorem original :
    Tendsto (fun n : ℕ => (minimum n : ℝ) / (n : ℝ))
      atTop (nhds (5 / 6 : ℝ)) :=
  Erdos136.erdos_136

theorem finite_strict_lower {n : ℕ} (hn : 4 ≤ n) :
    5 * (n - 1) < 6 * minimum n :=
  JSP000140.upstream_strict_lower hn

theorem genuine_eventual_colourings (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, Colorable n k ∧
      (k : ℝ) < (5 / 6 + ε) * (n : ℝ) := by
  filter_upwards [JSP000140.eventually_near_optimal ε hε,
    eventually_ge_atTop (2 : ℕ)] with n hn hn2
  obtain ⟨k, χ, hχ, hk⟩ := hn
  exact ⟨k, (JSP000140.pairColorable_iff hn2).mp ⟨χ, hχ⟩, hk⟩

end Verify140
