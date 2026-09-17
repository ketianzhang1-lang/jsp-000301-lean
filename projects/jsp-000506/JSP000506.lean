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

omit [DecidableEq α] in
lemma mass_nonneg (A : Finset (Finset α)) : 0 ≤ mass A := by
  unfold mass
  positivity

omit [DecidableEq α] in
lemma mass_univ : mass (univ : Finset (Finset α)) = 1 := by
  simp [mass, Fintype.card_finset]

omit [DecidableEq α] in
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

omit [DecidableEq α] in
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
  have hp : (0 : ℚ) < (2 : ℚ) ^ Fintype.card α := by positivity
  unfold mass
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hp (mul_pos hp hp)).2
  nlinarith [mul_le_mul_of_nonneg_right hq hp.le]

set_option maxHeartbeats 800000 in
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
    dsimp [E]
    rw [mass_event_compl (fun s => χ s ≤ ζ s + g)]
    exact hgood
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
    have ht' : χ s ≤ k := by simpa [D] using ht
    change t ∈ event _
    simp only [mem_event]
    exact (hmono hst).trans ht'
  have huUpper : IsUpperSet (U : Set (Finset α)) := by
    intro s t hst hs
    have hs' : χ sᶜ ≤ k + g := by simpa [U] using hs
    change t ∈ event _
    simp only [mem_event]
    exact (hmono (compl_subset_compl.mpr hst)).trans hs'
  have hcorr := mass_anticorrelation hdLower huUpper
  have hcov := mass_cover hcover
  have hU : (98 : ℚ) / 100 < mass U := by
    have hnum : mass D ≤ mass D * mass U + (1 : ℚ) / 1000 := by linarith only [hcorr, hcov, hEc]
    by_contra! hnot
    have hmul := mul_le_mul_of_nonneg_left hnot (mass_nonneg D)
    nlinarith only [hD, hnum, hmul]
  have heqU : mass U = mass (event fun s => χ s ≤ k + g) :=
    mass_event_compl (fun s => χ s ≤ k + g)
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

/-! Simple labelled graphs: an edge is an unordered pair represented uniquely
by its increasingly ordered endpoints. A subset of `Edge n` is precisely a
simple graph on `Fin n`. The uniform cube is therefore G(n,1/2). -/

def Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
deriving Fintype, DecidableEq

attribute [local instance] Classical.propDecidable

def Proper {n : ℕ} (s : Finset (Edge n)) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∀ e ∈ s, c e.val.1 ≠ c e.val.2

def CoProper {n : ℕ} (s : Finset (Edge n)) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∃ t : Fin k → Bool,
    ∀ e : Edge n, c e.val.1 = c e.val.2 → (e ∈ s ↔ t (c e.val.1) = true)

lemma proper_n {n : ℕ} (s : Finset (Edge n)) : Proper s n := by
  refine ⟨id, ?_⟩
  intro e _
  exact ne_of_lt e.property

lemma proper_to_coProper {n k : ℕ} {s : Finset (Edge n)}
    (h : Proper s k) : CoProper s k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun _ => false, ?_⟩
  intro e he
  simp only [Bool.false_eq_true, iff_false]
  intro hes
  exact hc e hes he

lemma coProper_compl {n k : ℕ} {s : Finset (Edge n)}
    (h : CoProper s k) : CoProper sᶜ k := by
  obtain ⟨c, t, ht⟩ := h
  refine ⟨c, fun i => !(t i), ?_⟩
  intro e he
  simp only [mem_compl, ht e he, Bool.not_eq_true]
  cases t (c e.val.1) <;> simp

noncomputable def chi {n : ℕ} (s : Finset (Edge n)) : ℕ :=
  Nat.find (⟨n, proper_n s⟩ : ∃ k, Proper s k)

noncomputable def zeta {n : ℕ} (s : Finset (Edge n)) : ℕ :=
  Nat.find (⟨n, proper_to_coProper (proper_n s)⟩ : ∃ k, CoProper s k)

lemma chi_spec {n : ℕ} (s : Finset (Edge n)) : Proper s (chi s) := by
  unfold chi
  exact Nat.find_spec _

lemma zeta_spec {n : ℕ} (s : Finset (Edge n)) : CoProper s (zeta s) := by
  unfold zeta
  exact Nat.find_spec _

lemma chi_mono (n : ℕ) : Monotone (@chi n) := by
  intro s t hst
  unfold chi
  apply Nat.find_min'
  obtain ⟨c, hc⟩ := chi_spec t
  exact ⟨c, fun e he => hc e (hst he)⟩

lemma zeta_le_chi {n : ℕ} (s : Finset (Edge n)) : zeta s ≤ chi s := by
  unfold zeta
  apply Nat.find_min'
  exact proper_to_coProper (chi_spec s)

lemma zeta_compl {n : ℕ} (s : Finset (Edge n)) : zeta sᶜ = zeta s := by
  apply Nat.le_antisymm
  · unfold zeta
    apply Nat.find_min'
    exact coProper_compl (zeta_spec s)
  · unfold zeta
    apply Nat.find_min'
    simpa only [compl_compl] using coProper_compl (zeta_spec sᶜ)

/-- Proposition 3 of Heckel's paper, for every finite graph order, including
zero. Probability is exact uniform counting on all simple labelled graphs.
The only premise is the stated 0.999 gap-probability hypothesis. -/
theorem heckel_proposition3 (n g : ℕ)
    (h : (999 : ℚ) / 1000 ≤
      mass (event fun s : Finset (Edge n) => chi s - zeta s ≤ g)) :
    ∃ k : ℕ, (9 : ℚ) / 10 <
      mass (event fun s : Finset (Edge n) => k ≤ chi s ∧ chi s ≤ k + g) := by
  apply concentration_reduction chi zeta g (chi_mono n) zeta_compl zeta_le_chi
  simpa only [Nat.sub_le_iff_le_add, Nat.add_comm] using h

end JSP000506
