import OriginalQuestion

/- Independent audit specification from He--Tang, Problem 1.1, Remark 1.2,
Definition 1.3. This file is an audit harness, not submitted source. -/
namespace Verify636
open Finset Filter
open scoped Topology
universe u

/-- Maximum number of occurring subset sizes, with literal exact multiplicity
and the ordinary inclusion relation, on an n-element ground set. -/
noncomputable def profile (n r : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun F : Finset (Finset (Fin n)) =>
    (∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B) ∧
    (∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r))).sup
      (fun F => (F.image Finset.card).card)

theorem profile_eq (n r : ℕ) : profile n r = JSP000636.exactExtremal n r := by
  rfl

/-- The original exact-r existence and impossibility assertions on arbitrary
finite types, with the level condition expanded in the audit statement. -/
theorem original :
    ∀ r ≥ 2, ∃ N ≤ 2*r+4*Nat.sqrt r+7,
      ∀ (α : Type u) [Fintype α], N < Fintype.card α →
        (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          (∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r) ∧
          F.card = r*(Fintype.card α-3)) ∧
        ¬ (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          (∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r) ∧
          F.card = r*(Fintype.card α-2)) := by
  simpa only [JSP000636.ExactMultiplicityOn] using
    JSP000636.original_threshold_question.{u}

/-- Original question plus least-cutoff semantics and all additional
quantitative assertions made by this submission. -/
theorem intended :
    (∀ r ≥ 2, ∃ N ≤ 2*r+4*Nat.sqrt r+7,
      ∀ (α : Type u) [Fintype α], N < Fintype.card α →
        (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          (∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r) ∧
          F.card = r*(Fintype.card α-3)) ∧
        ¬ (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          (∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r) ∧
          F.card = r*(Fintype.card α-2))) ∧
    (∀ r ≥ 2,
      (∀ n > JSP000636.threshold r, profile n r = n-3) ∧
      (∀ N, (∀ n > N, profile n r = n-3) → JSP000636.threshold r ≤ N)) ∧
    (∀ r ≥ 4, 2*r+2 ≤ JSP000636.threshold r ∧
      JSP000636.threshold r ≤ 2*r+4*Nat.sqrt r+7) ∧
    Tendsto (fun r : ℕ => (JSP000636.threshold r : ℝ)/r) atTop (𝓝 (2 : ℝ)) := by
  refine ⟨original, ?_, JSP000636.threshold_bounds, JSP000636.threshold_ratio_tendsto⟩
  intro r hr
  simpa only [profile_eq] using JSP000636.threshold_exact_spec r hr

end Verify636
