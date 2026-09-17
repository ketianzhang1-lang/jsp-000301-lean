/-
Statement adapted from the Formal Conjectures Authors (2026), Apache-2.0,
FormalConjectures/ErdosProblems/886.lean at 40e7c98697de6f66b8cbdbf641749ab39ed9c152.
Only metadata attributes are omitted. This project supplies the proof.
-/
import JSP000737
open Nat Filter
namespace Erdos886
theorem erdos_886.variants.rosenfeld_bound :
    ∀ C > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
    (((divisors n).filter (fun (d : ℕ) =>
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
      ≤ 1 + C ^ 2 := JSP000737.rosenfeld_bound
end Erdos886
