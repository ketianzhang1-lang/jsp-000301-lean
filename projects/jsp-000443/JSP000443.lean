import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
An independently written formalization of the elementary two-step-neighborhood
bound for C4 versus star Ramsey numbers. This is a known upper-bound component
of JSP-000443 / Erdos 552, not a resolution of its open exact-value question.
-/

open Finset

namespace JSP000443

/-- A (not necessarily induced) cycle on four distinct vertices.
The four edge hypotheses imply the four remaining inequalities. -/
def HasC4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A not-necessarily-induced star with n distinct leaves. -/
def HasStar {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ leaves : Fin n ↪ V, ∀ i, G.Adj v (leaves i)

/-- The explicit four-vertex predicate is ordinary graph-copy containment. -/
theorem hasC4_iff_copy {V : Type*} (G : SimpleGraph V) :
    HasC4 G ↔ Nonempty ((SimpleGraph.cycleGraph 4).Copy G) := by
  classical
  constructor
  · rintro ⟨a, b, c, d, hac, hbd, hab, hbc, hcd, hda⟩
    let f : Fin 4 → V := ![a, b, c, d]
    have hinj : Function.Injective f := by
      intro i j hij
      have hab' := hab.ne
      have hbc' := hbc.ne
      have hcd' := hcd.ne
      have hda' := hda.ne
      fin_cases i <;> fin_cases j <;> simp_all [f]
    refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph_adj, SimpleGraph.adj_comm]
    all_goals exact False.elim ((by decide : (-2 : Fin 4) ≠ 1) hij)
  · rintro ⟨f⟩
    exact ⟨f 0, f 1, f 2, f 3,
      f.injective.ne (by decide), f.injective.ne (by decide),
      f.toHom.map_adj (by decide), f.toHom.map_adj (by decide),
      f.toHom.map_adj (by decide), f.toHom.map_adj (by decide)⟩

/-- The explicit star predicate is a non-induced complete-bipartite copy. -/
theorem hasStar_iff_copy {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    HasStar G n ↔ Nonempty ((completeBipartiteGraph (Fin 1) (Fin n)).Copy G) := by
  classical
  constructor
  · rintro ⟨v, leaves, hv⟩
    let f : Fin 1 ⊕ Fin n → V := Sum.elim (fun _ => v) leaves
    have hi : Function.Injective f := by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Subsingleton.elim _ _)
        | inr b => exact False.elim ((hv b).ne hab)
      | inr a =>
        cases b with
        | inl b => exact False.elim ((hv a).ne hab.symm)
        | inr b => exact congrArg Sum.inr (leaves.injective hab)
    refine ⟨⟨⟨f, ?_⟩, hi⟩⟩
    intro a b hab
    cases a <;> cases b <;> simp_all [f, completeBipartiteGraph, SimpleGraph.adj_comm]
  · rintro ⟨f⟩
    refine ⟨f (Sum.inl 0), ⟨fun i => f (Sum.inr i), ?_⟩, ?_⟩
    · intro i j h
      exact Sum.inr.inj (f.injective h)
    · intro i
      exact f.toHom.map_adj (by simp [completeBipartiteGraph])

section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem hasStar_iff_degree (n : ℕ) :
    HasStar G n ↔ ∃ v : V, n ≤ G.degree v := by
  classical
  constructor
  · rintro ⟨v, f, hf⟩
    refine ⟨v, ?_⟩
    let e : Fin n ↪ G.neighborSet v :=
      ⟨fun i => ⟨f i, hf i⟩, fun i j h => f.injective (congrArg Subtype.val h)⟩
    simpa only [Fintype.card_fin, G.card_neighborSet_eq_degree] using
      Fintype.card_le_of_embedding e
  · rintro ⟨v, hv⟩
    have hc : Fintype.card (Fin n) ≤ Fintype.card (G.neighborSet v) := by
      simpa only [Fintype.card_fin, G.card_neighborSet_eq_degree] using hv
    obtain ⟨e⟩ := (Function.Embedding.nonempty_iff_card_le).mpr hc
    exact ⟨v, e.trans (Function.Embedding.subtype _), fun i => (e i).property⟩

/-- Distinct first steps have disjoint sets of second steps, after erasing
the starting vertex; otherwise the two paths form a four-cycle. -/
theorem second_steps_disjoint (h : ¬ HasC4 G) (v : V) :
    (↑(G.neighborFinset v) : Set V).PairwiseDisjoint
      (fun u => (G.neighborFinset u).erase v) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro c hca hcb
  have hca' := Finset.mem_erase.mp hca
  have hcb' := Finset.mem_erase.mp hcb
  apply h
  exact ⟨v, a, c, b, Ne.symm hca'.1, hab,
    (G.mem_neighborFinset _ _).mp ha, (G.mem_neighborFinset _ _).mp hca'.2,
    ((G.mem_neighborFinset _ _).mp hcb'.2).symm,
    ((G.mem_neighborFinset _ _).mp hb).symm⟩

/-- Rooted two-step counting, retaining the actual degree of the root. -/
theorem rooted_degree_bound (h : ¬ HasC4 G) (d : ℕ)
    (hd : ∀ u, d ≤ G.degree u) (v : V) :
    G.degree v * (d - 1) ≤ Fintype.card V - 1 := by
  classical
  let S := (G.neighborFinset v).biUnion fun u => (G.neighborFinset u).erase v
  have hcard : S.card = ∑ u ∈ G.neighborFinset v, (G.degree u - 1) := by
    rw [Finset.card_biUnion (second_steps_disjoint G h v)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.card_erase_of_mem]
    · rfl
    · exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hu).symm
  have hsub : S ⊆ Finset.univ.erase v := by
    intro u hu
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ _⟩
  calc
    G.degree v * (d - 1) = ∑ _u ∈ G.neighborFinset v, (d - 1) := by simp
    _ ≤ ∑ u ∈ G.neighborFinset v, (G.degree u - 1) :=
      Finset.sum_le_sum fun u _ => Nat.sub_le_sub_right (hd u) 1
    _ = S.card := hcard.symm
    _ ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
    _ = Fintype.card V - 1 := by simp

theorem minimum_degree_bound (h : ¬ HasC4 G) (d : ℕ)
    (hd : ∀ u, d ≤ G.degree u) (v : V) :
    d * (d - 1) ≤ Fintype.card V - 1 :=
  (Nat.mul_le_mul_right (d - 1) (hd v)).trans (rooted_degree_bound G h d hd v)

end Finite

/-- Every red/blue coloring of K_N has a red C4 or a blue n-leaf star. -/
def RamseyBound (n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasC4 G ∨ HasStar Gᶜ n

theorem ramseyBound_mono {n N M : ℕ} (hNM : N ≤ M)
    (hN : RamseyBound n N) : RamseyBound n M := by
  classical
  intro G
  let e : Fin N ↪ Fin M :=
    ⟨Fin.castLE hNM, fun _ _ h => Fin.ext (congrArg (fun x : Fin M => x.val) h)⟩
  rcases hN (G.comap e) with h | h
  · rcases h with ⟨a, b, c, d, hac, hbd, hab, hbc, hcd, hda⟩
    exact Or.inl ⟨e a, e b, e c, e d, e.injective.ne hac, e.injective.ne hbd,
      hab, hbc, hcd, hda⟩
  · rcases h with ⟨v, f, hf⟩
    refine Or.inr ⟨e v, f.trans e, ?_⟩
    intro i
    have hi := hf i
    change e v ≠ e (f i) ∧ ¬ G.Adj (e v) (e (f i))
    exact ⟨e.injective.ne hi.1, hi.2⟩

theorem ramsey_bound_of_arithmetic (n N : ℕ) (hN : 0 < N)
    (harith : N - 1 < (N - n) * (N - n - 1)) : RamseyBound n N := by
  classical
  intro G
  by_contra! h
  have hd : ∀ v, N - n ≤ G.degree v := by
    intro v
    have hs : Gᶜ.degree v < n := by
      by_contra! hh
      exact h.2 ((hasStar_iff_degree Gᶜ n).mpr ⟨v, hh⟩)
    rw [G.degree_compl] at hs
    have hdeg := G.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hs hdeg
    omega
  have hb := minimum_degree_bound G h.1 (N - n) hd ⟨0, hN⟩
  simp only [Fintype.card_fin] at hb
  omega

/-- Uniform classical upper bound, including the zero-leaf convention. -/
theorem ramsey_bound_sqrt (n : ℕ) :
    RamseyBound n (n + Nat.sqrt n + 2) := by
  apply ramsey_bound_of_arithmetic n _ (by omega)
  have hs := Nat.lt_succ_sqrt n
  have h1 : n + Nat.sqrt n + 2 - n = Nat.sqrt n + 2 := by omega
  have h2 : n + Nat.sqrt n + 2 - 1 = n + Nat.sqrt n + 1 := by omega
  rw [h1, h2]
  have h3 : Nat.sqrt n + 2 - 1 = Nat.sqrt n + 1 := by omega
  rw [h3]
  nlinarith

/-- For positive even k, the square case improves by one vertex.
Equality in the counting bound would force odd degree at every vertex of
an odd-order graph, contradicting the degree-sum identity. -/
theorem ramsey_bound_even_square (k : ℕ) (hk : 0 < k) (heven : k % 2 = 0) :
    RamseyBound (k ^ 2) (k ^ 2 + k + 1) := by
  classical
  intro G
  by_contra! h
  have hd : ∀ v, k + 1 ≤ G.degree v := by
    intro v
    have hs : Gᶜ.degree v < k ^ 2 := by
      by_contra! hh
      exact h.2 ((hasStar_iff_degree Gᶜ (k ^ 2)).mpr ⟨v, hh⟩)
    rw [G.degree_compl] at hs
    have hdeg := G.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hs hdeg
    omega
  have hreg : ∀ v, G.degree v = k + 1 := by
    intro v
    have hb := rooted_degree_bound G h.1 (k + 1) hd v
    simp only [Fintype.card_fin, Nat.add_sub_cancel] at hb
    have hlow := hd v
    nlinarith
  have hs := G.sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hs
  have hm := congrArg (fun x : ℕ => x % 2) hs
  simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, heven] at hm

/-- The least N with the usual red-C4 / blue-star Ramsey property. -/
noncomputable def c4StarRamsey (n : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨n + Nat.sqrt n + 2, ramsey_bound_sqrt n⟩ : ∃ N, RamseyBound n N)

theorem c4StarRamsey_le_sqrt (n : ℕ) : c4StarRamsey n ≤ n + Nat.sqrt n + 2 := by
  classical
  exact Nat.find_le (ramsey_bound_sqrt n)

theorem c4StarRamsey_le_of_bound {n N : ℕ} (h : RamseyBound n N) :
    c4StarRamsey n ≤ N := by
  classical
  exact Nat.find_le h

theorem c4StarRamsey_lower {n N : ℕ} (h : ¬ RamseyBound n N) :
    N < c4StarRamsey n := by
  classical
  by_contra! hh
  exact h (ramseyBound_mono hh (Nat.find_spec _))

/-- Codegree at most one suffices to exclude a four-cycle. -/
theorem noC4_of_common_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ a c : V, a ≠ c →
      ((Finset.univ.filter fun b => G.Adj a b ∧ G.Adj c b).card ≤ 1)) : ¬ HasC4 G := by
  rintro ⟨a, b, c, d, hac, hbd, hab, hbc, hcd, hda⟩
  apply hbd
  apply Finset.card_le_one.mp (h a c hac)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hab, hbc.symm⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hda.symm, hcd⟩

/-- Adjacency bitmasks of a 20-vertex orthogonal-polarity construction over
GF(4), with one absolute point deleted. The generator is supplied separately;
all properties needed below are checked by the Lean kernel from these rows. -/
def row20 (i : Fin 20) : ℕ :=
  ([1015808, 37136, 50248, 41508, 74754, 266760, 147716, 555008, 133698,
    67880, 264212, 526208, 278690, 131224, 69828, 524303, 16913, 270657,
    136225, 34945] : List ℕ)[i.val]!

def polarity20 : SimpleGraph (Fin 20) where
  Adj a b := (row20 a).testBit b.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel polarity20.Adj := fun _ _ => inferInstanceAs (Decidable (_ = true))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem polarity20_noC4 : ¬ HasC4 polarity20 := by
  apply noC4_of_common_neighbors
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem polarity20_degree : ∀ v, 4 ≤ polarity20.degree v := by decide +kernel

theorem polarity20_noStar_compl : ¬ HasStar polarity20ᶜ 16 := by
  rw [hasStar_iff_degree]
  push Not
  intro v
  have hv := polarity20_degree v
  rw [polarity20.degree_compl]
  simp only [Fintype.card_fin]
  omega

/-- A fully checked exact special value of the open parameter problem. -/
theorem c4StarRamsey_sixteen : c4StarRamsey 16 = 21 := by
  have hl : 20 < c4StarRamsey 16 :=
    c4StarRamsey_lower fun h => (h polarity20).elim polarity20_noC4 polarity20_noStar_compl
  have hu : c4StarRamsey 16 ≤ 21 := by
    apply c4StarRamsey_le_of_bound
    simpa using ramsey_bound_even_square 4 (by omega) (by decide)
  omega

end JSP000443
