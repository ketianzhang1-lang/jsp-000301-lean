/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modified: exact B definition and two solved theorem types transcribed from
FormalConjectures/ErdosProblems/367.lean at
40e7c98697de6f66b8cbdbf641749ab39ed9c152.
Research metadata is omitted; answer(False) is expanded to False.
The proofs below are supplied by the new JSP000303 module.
-/
import JSP000303

open scoped BigOperators
open Asymptotics Filter

namespace Erdos367

def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

theorem erdos_367.variants.k_ge_three_lower :
    ∃ c > (0 : ℝ), ∃ᶠ (n : ℕ) in atTop,
      c * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        ((∏ m ∈ Finset.Ico n (n + 3), B 2 m : ℕ) : ℝ) :=
  JSP000303.erdos_367_k_three_lower

theorem erdos_367.parts.ii : False ↔ ∀ k : ℕ, 1 ≤ k →
    (fun n ↦ ((∏ m ∈ Finset.Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  constructor
  · exact False.elim
  · intro h
    apply JSP000303.not_quadratic_bound 3 (by norm_num)
    simpa only [B, JSP000303.B, Real.rpow_two] using h 3 (by norm_num)

end Erdos367
