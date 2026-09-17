import Erdos16Density

/-!
Reference shape follows Google DeepMind's Formal Conjectures Erdős 16 statement
at commit 40e7c98697de6f66b8cbdbf641749ab39ed9c152. The source labels the
one-progression question as answered negatively. No `answer` placeholder or
unproved reference theorem is imported here.
-/
namespace Erdos16Reference
open Nat Filter Set
open scoped Topology

def ExceptionalSet : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p}

def DensityZero (S : Set ℕ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (count (· ∈ S) n : ℝ) / (n : ℝ)) atTop (𝓝 0)

/-- Checked without weakening or adding assumptions to the reference statement. -/
theorem erdos_16 :
    ¬ ∃ A B : Set ℕ, ExceptionalSet = A ∪ B ∧
      (∃ a d : ℕ, d > 0 ∧ A = {x | ∃ m : ℕ, x = a + m * d}) ∧
      DensityZero B := by
  exact Erdos16Density.no_decomposition

end Erdos16Reference
