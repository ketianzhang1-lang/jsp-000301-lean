/-
The definition and Monier theorem type below are adapted from
The Formal Conjectures Authors (2026), licensed under Apache 2.0:
https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean
Only research metadata is omitted. No unproved source theorem is imported.
-/
import JSP000883

namespace Erdos1063

noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

theorem erdos_1063.variants.monier_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k.factorial :=
  JSP000883.monier_upper_bound hk

theorem original_least_is_admissible {k : ℕ} (hk : 3 ≤ k) :
    2 * k ≤ n k ∧ ∃ i0 < k, ¬ (n k - i0) ∣ (n k).choose k ∧
      ∀ i < k, i ≠ i0 → (n k - i) ∣ (n k).choose k :=
  JSP000883.least_is_admissible hk

end Erdos1063
