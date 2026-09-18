import JSP000140Bridge
import ErdosProblems.Erdos136

/-! Our exact minimum-palette bridge joins our strict finite lower bound with
an attributed complete upper construction. The existing upper proof and all
its dependencies are fixed in UPSTREAM.json. -/
namespace JSP000140
open Filter
open scoped Topology

theorem minPalette_tendsto :
    Tendsto (fun n : ℕ => (minPalette n : ℝ) / (n : ℝ)) atTop (nhds (5 / 6 : ℝ)) := by
  apply Erdos136.erdos_136.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [minPalette_eq hn]

theorem minPalette_asymptotic :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (minPalette n : ℝ))
      (fun n : ℕ => (5 / 6 : ℝ) * (n : ℝ)) := by
  exact Erdos136.isEquivalent_of_tendsto_normalized _ _ (by norm_num) minPalette_tendsto

theorem eventually_near_optimal (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ (k : ℕ) (χ : Coloring n k),
      Admissible χ ∧ (k : ℝ) < (5 / 6 + ε) * (n : ℝ) := by
  have h := (tendsto_order.mp minPalette_tendsto).2 (5 / 6 + ε) (by linarith)
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  obtain ⟨χ,hχ⟩ := minPalette_spec n
  refine ⟨minPalette n, χ, hχ, ?_⟩
  exact (div_lt_iff₀ (by exact_mod_cast hn0 : (0 : ℝ) < n)).mp hn

theorem upstream_strict_lower {n : ℕ} (hn : 4 ≤ n) :
    5 * (n - 1) < 6 * Erdos136.erdos136Fun n := by
  rw [← minPalette_eq (by omega : 2 ≤ n)]
  exact minPalette_strict_lower hn

theorem upstream_integer_lower {n : ℕ} (hn : 4 ≤ n) :
    5 * (n - 1) / 6 + 1 ≤ Erdos136.erdos136Fun n := by
  rw [← minPalette_eq (by omega : 2 ≤ n)]
  exact minPalette_integer_lower hn

/-- Full asymptotic answer, finite strict lower bound, and eventual genuine
colourings in our original model with arbitrarily small linear surplus. -/
theorem jsp_000140 :
    (∀ n : ℕ, 4 ≤ n → 5 * (n - 1) / 6 + 1 ≤ minPalette n) ∧
    Tendsto (fun n : ℕ => (minPalette n : ℝ) / (n : ℝ)) atTop (nhds (5 / 6 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ (k : ℕ) (χ : Coloring n k),
      Admissible χ ∧ (k : ℝ) < (5 / 6 + ε) * (n : ℝ)) :=
  ⟨fun _ hn => minPalette_integer_lower hn, minPalette_tendsto, eventually_near_optimal⟩

end JSP000140
