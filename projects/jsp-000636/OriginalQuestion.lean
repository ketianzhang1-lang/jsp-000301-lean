import Asymptotics

/-!
We express the original Erdős–Trotter threshold-estimate question on an
arbitrary finite ground type. The map lemmas preserve actual distinct subsets,
inclusion, level multiplicities and the total number of members.
Mathematical credit for the underlying bounds remains with He and Tang.
-/

namespace JSP000636
open Finset Filter
open scoped Topology
universe u v

/-- Exactly r distinct members at each occurring size, on any ground type. -/
def ExactMultiplicityOn {α : Type u} (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, (F.filter (fun B => B.card = A.card)).card = r

/-- Relabel both the ground elements and the family, without deduplication. -/
def mapFamily {α : Type u} {β : Type v} (e : α ↪ β)
    (F : Finset (Finset α)) : Finset (Finset β) :=
  F.map ⟨Finset.map e, Finset.map_injective e⟩

theorem mapFamily_card {α : Type u} {β : Type v} (e : α ↪ β)
    (F : Finset (Finset α)) : (mapFamily e F).card = F.card := by
  simp [mapFamily]

theorem mapFamily_level_card {α : Type u} {β : Type v} (e : α ↪ β)
    (F : Finset (Finset α)) (t : ℕ) :
    ((mapFamily e F).filter (fun A => A.card = t)).card =
      (F.filter (fun A => A.card = t)).card := by
  simp [mapFamily, Finset.filter_map]

theorem mapFamily_antichain_iff {α : Type u} {β : Type v} (e : α ↪ β)
    (F : Finset (Finset α)) :
    IsAntichain (· ⊆ ·) (↑(mapFamily e F) : Set (Finset β)) ↔
      IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) := by
  constructor
  · intro h A hA B hB hne hsub
    apply h (x := A.map e) (y := B.map e)
    · exact Finset.mem_map.mpr ⟨A,hA,rfl⟩
    · exact Finset.mem_map.mpr ⟨B,hB,rfl⟩
    · exact fun heq => hne (Finset.map_injective e heq)
    · exact Finset.map_subset_map.mpr hsub
  · intro h A hA B hB hne hsub
    obtain ⟨C,hC,rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨D,hD,rfl⟩ := Finset.mem_map.mp hB
    exact h hC hD (fun heq => hne (congrArg (Finset.map e) heq))
      (Finset.map_subset_map.mp hsub)

theorem mapFamily_exact_iff {α : Type u} {β : Type v} (e : α ↪ β)
    (F : Finset (Finset α)) (r : ℕ) :
    ExactMultiplicityOn r (mapFamily e F) ↔ ExactMultiplicityOn r F := by
  constructor
  · intro h A hA
    have hh := h (A.map e) (Finset.mem_map.mpr ⟨A,hA,rfl⟩)
    simpa only [Finset.card_map,mapFamily_level_card] using hh
  · intro h A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_map.mp hA
    simpa only [Function.Embedding.coeFn_mk,Finset.card_map,mapFamily_level_card]
      using h B hB

/-- The universal upper bound applies to every finite ground set. -/
theorem finite_type_card_le (α : Type u) [Fintype α] (r : ℕ)
    (hn : 4 ≤ Fintype.card α) (hr : 2 ≤ r)
    (F : Finset (Finset α))
    (ha : IsAntichain (· ⊆ ·) (↑F : Set (Finset α)))
    (hm : ExactMultiplicityOn r F) : F.card ≤ r*(Fintype.card α-3) := by
  let e := (Fintype.equivFin α).toEmbedding
  have h := exact_multiplicity_card_le (Fintype.card α) r hn hr (mapFamily e F)
    ((mapFamily_antichain_iff e F).mpr ha) ((mapFamily_exact_iff e F r).mpr hm)
  simpa only [mapFamily_card] using h

/-- The exact-r construction transfers to every finite ground set of this size. -/
theorem finite_type_attaining_family (α : Type u) [Fintype α] (r : ℕ)
    (hr : 2 ≤ r) (hn : 2*r+4*Nat.sqrt r+8 ≤ Fintype.card α) :
    ∃ F : Finset (Finset α),
      IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
      ExactMultiplicityOn r F ∧ F.card = r*(Fintype.card α-3) := by
  obtain ⟨F,ha,hm,_,hc⟩ := exact_attaining_family (Fintype.card α) r hr hn
  let e := (Fintype.equivFin α).symm.toEmbedding
  refine ⟨mapFamily e F,?_,?_,?_⟩
  · exact (mapFamily_antichain_iff e F).mpr ((antichain_iff_isAntichain F).mp ha)
  · exact (mapFamily_exact_iff e F r).mpr hm
  · simpa only [mapFamily_card] using hc

/-- The literal original existence and impossibility assertions, uniformly in r
and in the finite ground set, with an explicit admissible cutoff. -/
theorem original_threshold_question :
    ∀ r ≥ 2, ∃ N ≤ 2*r+4*Nat.sqrt r+7,
      ∀ (α : Type u) [Fintype α], N < Fintype.card α →
        (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          ExactMultiplicityOn r F ∧ F.card = r*(Fintype.card α-3)) ∧
        ¬ (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          ExactMultiplicityOn r F ∧ F.card = r*(Fintype.card α-2)) := by
  intro r hr
  refine ⟨2*r+4*Nat.sqrt r+7,le_rfl,?_⟩
  intro α _ hn
  refine ⟨finite_type_attaining_family α r hr (by omega),?_⟩
  rintro ⟨F,ha,hm,hc⟩
  have hle := finite_type_card_le α r (by omega) hr F ha hm
  have hdiff : Fintype.card α-2 = (Fintype.card α-3)+1 := by omega
  rw [hc,hdiff,Nat.mul_add,Nat.mul_one] at hle
  omega

/-- Complete threshold-estimate endpoint: the original exact-r family statement,
the actual least threshold, all-parameter bounds and its sharp leading growth. -/
theorem jsp_000636 :
    (∀ r ≥ 2, ∃ N ≤ 2*r+4*Nat.sqrt r+7,
      ∀ (α : Type u) [Fintype α], N < Fintype.card α →
        (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          ExactMultiplicityOn r F ∧ F.card = r*(Fintype.card α-3)) ∧
        ¬ (∃ F : Finset (Finset α),
          IsAntichain (· ⊆ ·) (↑F : Set (Finset α)) ∧
          ExactMultiplicityOn r F ∧ F.card = r*(Fintype.card α-2))) ∧
    (∀ r ≥ 2,
      (∀ n > threshold r, exactExtremal n r = n-3) ∧
      (∀ N, (∀ n > N, exactExtremal n r = n-3) → threshold r ≤ N)) ∧
    (∀ r ≥ 4, 2*r+2 ≤ threshold r ∧ threshold r ≤ 2*r+4*Nat.sqrt r+7) ∧
    Tendsto (fun r : ℕ => (threshold r : ℝ)/r) atTop (𝓝 (2 : ℝ)) := by
  exact ⟨original_threshold_question,threshold_exact_spec,
    threshold_bounds,threshold_ratio_tendsto⟩

end JSP000636
