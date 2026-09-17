import JSP000749.Counting
import JSP000749.Estimates

namespace JSP000749
open Finset
open scoped Classical

/-- A simple hypergraph is a finite family of finite sets, so duplicate edges
are not counted twice. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- Weak proper k-colourability: every edge contains vertices of different colours. -/
def Colorable {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- Every edge contains exactly n distinct vertices. -/
def Uniform {V : Type*} (H : Hypergraph V) (n : ℕ) : Prop :=
  ∀ e ∈ H, e.card = n

/-- The space of all n-element subsets of an N-point ground set. -/
abbrev Edge (N n : ℕ) := ↥((Finset.univ : Finset (Fin N)).powersetCard n)

lemma card_edge (N n : ℕ) : Fintype.card (Edge N n) = N.choose n := by
  simp [Edge]

/-- An edge lies wholly inside one of the two parts of a binary partition. -/
def Monochromatic {N n : ℕ} (S : Finset (Fin N)) (e : Edge N n) : Prop :=
  e.1 ⊆ S ∨ e.1 ⊆ Sᶜ

lemma monochromatic_card_lower {N n : ℕ} (S T : Finset (Fin N))
    (hT : T ⊆ S ∨ T ⊆ Sᶜ) :
    T.card.choose n ≤ Fintype.card {e : Edge N n // Monochromatic S e} := by
  classical
  let emb : ↥(T.powersetCard n) → {e : Edge N n // Monochromatic S e} := fun s =>
    ⟨⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.2).2⟩⟩,
      hT.elim (fun h => Or.inl ((Finset.mem_powersetCard.mp s.2).1.trans h))
        (fun h => Or.inr ((Finset.mem_powersetCard.mp s.2).1.trans h))⟩
  have hinj : Function.Injective emb := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun z : {e : Edge N n // Monochromatic S e} => z.1.1) h
  simpa only [Fintype.card_coe, Finset.card_powersetCard] using Fintype.card_le_of_injective emb hinj

/-- Every binary partition has a large colour class, and hence many monochromatic edges. -/
theorem majority_card_lower (n : ℕ) (S : Finset (Fin (2 * n ^ 2))) :
    (n ^ 2).choose n ≤ Fintype.card {e : Edge (2 * n ^ 2) n // Monochromatic S e} := by
  by_cases h : n ^ 2 ≤ S.card
  · exact (Nat.choose_le_choose n h).trans (monochromatic_card_lower S S (Or.inl Subset.rfl))
  · have hc : n ^ 2 ≤ Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    exact (Nat.choose_le_choose n hc).trans (monochromatic_card_lower S Sᶜ (Or.inr Subset.rfl))

/-- The classical probabilistic construction, expressed entirely as a finite
counting argument with every parameter explicit. -/
theorem exists_bounded_obstruction (n : ℕ) (hn : 2 ≤ n) :
    ∃ H : Hypergraph (Fin (2 * n ^ 2)), Uniform H n ∧
      H.card ≤ 4 * n ^ 2 * 2 ^ n ∧ ¬ Colorable H 2 := by
  classical
  let N := 2 * n ^ 2
  let a := 2 ^ (n + 1)
  let M := N * a
  let D := (n ^ 2).choose n
  have hNM : M = 4 * n ^ 2 * 2 ^ n := by dsimp [M, N, a]; rw [pow_succ]; ring
  have hpos : 0 < N.choose n := Nat.choose_pos (by dsimp [N]; nlinarith)
  have hDE : D ≤ N.choose n := Nat.choose_le_choose n (by dsimp [N]; omega)
  have hED : N.choose n ≤ a * D := binomial_ratio_bound n hn
  have hb : Fintype.card (Finset (Fin N)) *
      (Fintype.card (Edge N n) - D) ^ M < Fintype.card (Edge N n) ^ M := by
    simp only [Fintype.card_finset, Fintype.card_fin, card_edge]
    exact tuple_count_bound _ _ a N hpos hDE (by dsimp [a]; positivity)
      (by dsimp [N]; nlinarith) hED
  obtain ⟨f, hf⟩ := exists_hitting_tuple (fun (S : Finset (Fin N)) (e : Edge N n) =>
    Monochromatic S e) M D (majority_card_lower n) hb
  let H : Hypergraph (Fin N) := Finset.univ.image (fun i : Fin M => (f i).1)
  refine ⟨H, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_powersetCard.mp (f i).2).2
  · calc
      H.card ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_image_le
      _ = M := by simp
      _ = _ := hNM
  · rintro ⟨c, hc⟩
    let S : Finset (Fin N) := Finset.univ.filter (fun v => c v = 0)
    obtain ⟨i, hi⟩ := hf S
    have hei : (f i).1 ∈ H := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨u, hu, v, hv, hne⟩ := hc _ hei
    apply hne
    rcases hi with hi | hi
    · have hu0 : c u = 0 := (Finset.mem_filter.mp (hi hu)).2
      have hv0 : c v = 0 := (Finset.mem_filter.mp (hi hv)).2
      exact hu0.trans hv0.symm
    · have hu0 : c u ≠ 0 := by simpa [S] using (Finset.mem_compl.mp (hi hu))
      have hv0 : c v ≠ 0 := by simpa [S] using (Finset.mem_compl.mp (hi hv))
      apply Fin.ext
      have hcu := (c u).isLt
      have hcv := (c v).isLt
      have hcu0 : (c u).val ≠ 0 := by intro heq; exact hu0 (Fin.ext heq)
      have hcv0 : (c v).val ≠ 0 := by intro heq; exact hv0 (Fin.ext heq)
      omega

end JSP000749
