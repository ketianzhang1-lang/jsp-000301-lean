/-
Copyright (c) 2026. Released under the Apache 2.0 license.
AI-assisted formalization prepared for ketianzhang1-lang.
Mathematical source: Annika Heckel, Proposition 3,
On a question of Erdos and Gimbel on the cochromatic number (2024).
This is a scoped component, not a solution of the full asymptotic problem.
-/
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Tactic

namespace JSP000506
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def event (p : Finset α → Prop) : Finset (Finset α) :=
  by classical exact univ.filter p

noncomputable def mass (A : Finset (Finset α)) : ℚ :=
  (A.card : ℚ) / (2 : ℚ) ^ Fintype.card α

lemma mass_nonneg (A : Finset (Finset α)) : 0 ≤ mass A := by
  unfold mass
  positivity

lemma mass_univ : mass (univ : Finset (Finset α)) = 1 := by
  simp [mass, Fintype.card_finset]

lemma mass_mono {A B : Finset (Finset α)} (h : A ⊆ B) : mass A ≤ mass B := by
  unfold mass
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

lemma mass_compl (A : Finset (Finset α)) : mass Aᶜ = 1 - mass A := by
  unfold mass
  rw [card_compl, Nat.cast_sub (card_le_univ A), Fintype.card_finset]
  push_cast
  field_simp

lemma mass_union_le (A B : Finset (Finset α)) :
    mass (A ∪ B) ≤ mass A + mass B := by
  unfold mass
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_union_le A B

lemma mass_cover {A B C : Finset (Finset α)} (h : A ⊆ B ∪ C) :
    mass A ≤ mass B + mass C := (mass_mono h).trans (mass_union_le B C)

@[simp] lemma mem_event (p : Finset α → Prop) (s : Finset α) :
    s ∈ event p ↔ p s := by classical simp [event]

lemma mass_event_compl (p : Finset α → Prop) :
    mass (event fun s : Finset α => p sᶜ) = mass (event p) := by
  classical
  unfold mass
  congr 1
  exact_mod_cast (card_bij (fun s _ => sᶜ)
    (by intro s hs; simpa using hs)
    (by intro s hs t ht h; simpa using congrArg (fun x : Finset α => xᶜ) h)
    (by intro s hs; exact ⟨sᶜ, by simpa using hs, by simp⟩))

lemma mass_anticorrelation {A B : Finset (Finset α)}
    (hA : IsLowerSet (A : Set (Finset α)))
    (hB : IsUpperSet (B : Set (Finset α))) :
    mass (A ∩ B) ≤ mass A * mass B := by
  have h := hA.card_inter_le_finset hB
  have hq : (2 : ℚ) ^ Fintype.card α * (A ∩ B).card ≤
      (A.card : ℚ) * B.card := by exact_mod_cast h
  unfold mass
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ Fintype.card α)).mp
  field_simp
  nlinarith

/-- Heckel's concentration reduction on a uniform finite Boolean cube.
`χ` is increasing, `ζ` is invariant under complementation and bounded by `χ`.
If the gap is at most `g` with probability at least 0.999, some interval
of length `g` contains `χ` with probability strictly greater than 0.9. -/
theorem concentration_reduction (χ ζ : Finset α → ℕ) (g : ℕ)
    (hmono : Monotone χ) (hsym : ∀ s, ζ sᶜ = ζ s)
    (hle : ∀ s, ζ s ≤ χ s)
    (hgood : (999 : ℚ) / 1000 ≤ mass (event fun s => χ s ≤ ζ s + g)) :
    ∃ k : ℕ, (9 : ℚ) / 10 < mass (event fun s => k ≤ χ s ∧ χ s ≤ k + g) := by
  classical
  let P : ℕ → Prop := fun k => (1 : ℚ) / 20 < mass (event fun s => χ s ≤ k)
  have hex : ∃ k, P k := by
    refine ⟨(univ : Finset (Finset α)).sup χ, ?_⟩
    have he : event (fun s => χ s ≤ (univ : Finset (Finset α)).sup χ) = univ := by
      ext s
      simp only [mem_event, mem_univ, iff_true]
      exact le_sup (f := χ) (mem_univ s)
    dsimp [P]
    rw [he, mass_univ]
    norm_num
  let k := Nat.find hex
  let D := event fun s => χ s ≤ k
  let U := event fun s => χ sᶜ ≤ k + g
  let E := event fun s => χ sᶜ ≤ ζ sᶜ + g
  let L := event fun s => χ s < k
  let I := event fun s => k ≤ χ s ∧ χ s ≤ k + g
  have hD : (1 : ℚ) / 20 < mass D := Nat.find_spec hex
  have hL : mass L ≤ (1 : ℚ) / 20 := by
    by_cases hk : k = 0
    · have he : L = ∅ := by ext s; simp [L, hk]
      rw [he]
      norm_num [mass]
    · have hnot : ¬ P (k - 1) := Nat.find_min hex (by dsimp [k] at *; omega)
      have he : L = event (fun s => χ s ≤ k - 1) := by
        ext s
        simp only [L, mem_event]
        omega
      rw [he]
      exact le_of_not_gt hnot
  have hE : (999 : ℚ) / 1000 ≤ mass E := by
    simpa only [E, mass_event_compl] using hgood
  have hEc : mass Eᶜ ≤ (1 : ℚ) / 1000 := by
    rw [mass_compl]
    linarith
  have hcover : D ⊆ (D ∩ U) ∪ Eᶜ := by
    intro s hs
    by_cases he : s ∈ E
    · apply mem_union_left
      apply mem_inter.mpr ⟨hs, ?_⟩
      have hd : χ s ≤ k := by simpa [D] using hs
      have he' : χ sᶜ ≤ ζ sᶜ + g := by simpa [E] using he
      have hz := hle s
      rw [hsym] at he'
      change s ∈ event _
      simp only [mem_event]
      omega
    · exact mem_union_right _ (mem_compl.mpr he)
  have hdLower : IsLowerSet (D : Set (Finset α)) := by
    intro s t hst ht
    have ht' : χ t ≤ k := by simpa [D] using ht
    change s ∈ event _
    exact mem_event.mpr ((hmono hst).trans ht')
  have huUpper : IsUpperSet (U : Set (Finset α)) := by
    intro s t hst hs
    have hs' : χ sᶜ ≤ k + g := by simpa [U] using hs
    change t ∈ event _
    apply mem_event.mpr
    exact (hmono (compl_subset_compl.mpr hst)).trans hs'
  have hcorr := mass_anticorrelation hdLower huUpper
  have hcov := mass_cover hcover
  have hu1 : mass U ≤ 1 := by simpa using mass_mono (subset_univ U)
  have hU : (98 : ℚ) / 100 < mass U := by
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hD)) (sub_nonneg.mpr hu1)]
  have heqU : mass U = mass (event fun s => χ s ≤ k + g) := mass_event_compl _
  have hsplit : event (fun s => χ s ≤ k + g) ⊆ I ∪ L := by
    intro s hs
    simp only [mem_event] at hs
    simp only [I, L, mem_union, mem_event]
    omega
  have hsplitmass := mass_cover hsplit
  refine ⟨k, ?_⟩
  change (9 : ℚ) / 10 < mass I
  rw [← heqU] at hsplitmass
  linarith

end JSP000506
