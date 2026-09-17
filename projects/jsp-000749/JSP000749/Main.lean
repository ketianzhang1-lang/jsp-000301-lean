import JSP000749.Construction

/-!
# JSP-000749 / Erdos 901: a complete formalization of the classical upper-bound component

For every n >= 2 there is a simple n-uniform hypergraph on 2*n^2 vertices,
with at most 4*n^2*2^n edges, of weak chromatic number exactly three.
This is known mathematics, not a solution of the still open precise-order question.
The proof combines a finite union bound with the minimal-obstruction reduction.
-/
namespace JSP000749
open Finset
open scoped Classical

lemma colorable_mono_colors {V : Type*} {H : Hypergraph V} {k l : ℕ}
    (hkl : k ≤ l) (h : Colorable H k) : Colorable H l := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => (c v).castLE hkl, ?_⟩
  intro e he
  obtain ⟨u, hu, v, hv, hne⟩ := hc e he
  refine ⟨u, hu, v, hv, ?_⟩
  intro heq
  apply hne
  exact Fin.ext (congrArg (fun x : Fin l => x.val) heq)

/-- Exact weak chromatic number three, with no ambiguity about a minimum of an
empty set of colour counts. -/
def ExactlyThree {V : Type*} (H : Hypergraph V) : Prop :=
  Colorable H 3 ∧ ∀ k : ℕ, k < 3 → ¬ Colorable H k

/-- If deleting an edge permits two colours, recolouring one vertex of that edge
with a third colour suffices. All edges have at least two distinct vertices. -/
lemma three_colorable_of_erase {V : Type*} [DecidableEq V]
    {H : Hypergraph V} {e : Finset V} (he : e ∈ H)
    (hsize : ∀ f ∈ H, 2 ≤ f.card) (hc : Colorable (H.erase e) 2) :
    Colorable H 3 := by
  classical
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (hsize e he))
  obtain ⟨c, hc⟩ := hc
  let d : V → Fin 3 := fun v => if v = u then 2 else (c v).castLE (by decide)
  refine ⟨d, ?_⟩
  intro f hf
  by_cases huf : u ∈ f
  · obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (lt_of_lt_of_le (by decide : 1 < 2) (hsize f hf)) u
    refine ⟨u, huf, v, hv, ?_⟩
    intro heq
    have heq' := congrArg (fun x : Fin 3 => x.val) heq
    have huval : (d u).val = 2 := by simp [d]
    have hvval : (d v).val = (c v).val := by simp [d, hvu]
    rw [huval, hvval] at heq'
    have hcv := (c v).isLt
    omega
  · have hfe : f ≠ e := by intro h; subst f; exact huf hu
    obtain ⟨v, hv, w, hw, hne⟩ := hc f (Finset.mem_erase.mpr ⟨hfe, hf⟩)
    have hvu : v ≠ u := by intro h; subst v; exact huf hv
    have hwu : w ≠ u := by intro h; subst w; exact huf hw
    refine ⟨v, hv, w, hw, ?_⟩
    intro heq
    apply hne
    apply Fin.ext
    have heq' := congrArg (fun x : Fin 3 => x.val) heq
    simpa [d, hvu, hwu] using heq'

/-- Extracting a minimal non-two-colourable subhypergraph supplies exact
three-colourability without increasing its number of edges. -/
theorem minimal_obstruction {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (hsize : ∀ e ∈ H, 2 ≤ e.card) (hH : ¬ Colorable H 2) :
    ∃ G ⊆ H, ExactlyThree G ∧
      (∀ G' : Hypergraph V, G' ⊂ G → Colorable G' 2) := by
  classical
  obtain ⟨G, hGH, hG⟩ := exists_minimal_le_of_wellFoundedLT (fun G : Hypergraph V => ¬ Colorable G 2) H hH
  have hproper : ∀ G' : Hypergraph V, G' ⊂ G → Colorable G' 2 := by
    intro G' hlt
    by_contra hn
    exact (not_le_of_gt hlt) (hG.le_of_le hn hlt.le)
  have hne : G.Nonempty := by
    by_contra he
    have hz : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hG.prop
    subst G
    exact ⟨fun _ => 0, by simp⟩
  obtain ⟨e, he⟩ := hne
  have h3 : Colorable G 3 := three_colorable_of_erase he
    (fun f hf => hsize f (hGH hf)) (hproper (G.erase e) (Finset.erase_ssubset he))
  refine ⟨G, hGH, ⟨h3, ?_⟩, hproper⟩
  intro k hk hcol
  exact hG.prop (colorable_mono_colors (by omega : k ≤ 2) hcol)

/-- The full promised all-parameter upper-bound component. The ground set has
2*n^2 vertices, all edges have cardinality n, and the weak chromatic number is
exactly three. Every proper edge subfamily is two-colourable. -/
theorem jsp000749_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ H : Hypergraph (Fin (2 * n ^ 2)),
      Uniform H n ∧ H.card ≤ 4 * n ^ 2 * 2 ^ n ∧ ExactlyThree H ∧
      (∀ G : Hypergraph (Fin (2 * n ^ 2)), G ⊂ H → Colorable G 2) := by
  obtain ⟨H, hU, hcard, hH⟩ := exists_bounded_obstruction n hn
  obtain ⟨G, hGH, h3, hmin⟩ := minimal_obstruction H
    (fun e he => by rw [hU e he]; exact hn) hH
  exact ⟨G, fun e he => hU e (hGH he), (Finset.card_le_card hGH).trans hcard, h3, hmin⟩

/-- The attainable edge counts for arbitrary finite ground-set sizes, using the
original exact-three-colour condition. -/
def Attainable (n k : ℕ) : Prop :=
  ∃ N : ℕ, ∃ H : Hypergraph (Fin N), Uniform H n ∧ ExactlyThree H ∧ H.card = k

/-- The extremal function is the infimum of actual attainable edge counts.
The next theorem proves this set is nonempty for every n >= 2. -/
noncomputable def m (n : ℕ) : ℕ := sInf {k : ℕ | Attainable n k}

lemma attainable_nonempty (n : ℕ) (hn : 2 ≤ n) :
    {k : ℕ | Attainable n k}.Nonempty := by
  obtain ⟨H, hU, _, h3, _⟩ := jsp000749_upper_bound n hn
  exact ⟨H.card, 2 * n ^ 2, H, hU, h3, rfl⟩

/-- The infimum defining m(n) is attained; it is not the default infimum of an
empty set. -/
theorem m_attained (n : ℕ) (hn : 2 ≤ n) : Attainable n (m n) := by
  exact Nat.sInf_mem (attainable_nonempty n hn)

/-- An explicit version of the classical m(n) = O(n^2*2^n) upper bound. -/
theorem m_upper_bound (n : ℕ) (hn : 2 ≤ n) : m n ≤ 4 * n ^ 2 * 2 ^ n := by
  obtain ⟨H, hU, hcard, h3, _⟩ := jsp000749_upper_bound n hn
  have hmem : Attainable n H.card := ⟨2 * n ^ 2, H, hU, h3, rfl⟩
  exact (Nat.sInf_le hmem).trans hcard

/-- Positivity of the extremal value. -/
theorem m_positive (n : ℕ) (hn : 2 ≤ n) : 0 < m n := by
  obtain ⟨N, H, _, h3, hcard⟩ := m_attained n hn
  have hne : H.Nonempty := by
    by_contra h
    have hz : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    exact h3.2 2 (by decide) ⟨fun _ => 0, by simp [hz]⟩
  rw [← hcard]
  exact Finset.card_pos.mpr hne

end JSP000749
