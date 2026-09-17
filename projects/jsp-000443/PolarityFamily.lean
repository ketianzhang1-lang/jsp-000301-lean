import JSP000443
import Mathlib.FieldTheory.Finite.GaloisField

/-!
An independently written algebraic finite-field construction for the classical
C4/star Ramsey lower bound. This extends the finite n=16 certificate to a
parameterized family, not to a solution of the full open problem.
-/

namespace JSP000443
namespace PolarityFamily

variable (F : Type*) [Field F]

abbrev Vertex := (F × F) ⊕ F

/-- Affine points together with one point for each vertical direction. -/
def Incidence : Vertex F → Vertex F → Prop
  | .inl (a,b), .inl (c,d) => b + d = a * c
  | .inl (a,_), .inr c => a = c
  | .inr a, .inl (c,_) => c = a
  | .inr _, .inr _ => False

def graph : SimpleGraph (Vertex F) where
  Adj u v := u ≠ v ∧ Incidence F u v
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    cases u <;> cases v <;> simpa [Incidence, add_comm, mul_comm] using h.2⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- Two distinct vertices have at most one common neighbor. -/
theorem common_neighbor_unique (u v x y : Vertex F) (huv : u ≠ v)
    (hux : (graph F).Adj u x) (hvx : (graph F).Adj v x)
    (huy : (graph F).Adj u y) (hvy : (graph F).Adj v y) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  cases u with
  | inl u =>
    rcases u with ⟨a,b⟩
    cases v with
    | inl v =>
      rcases v with ⟨c,d⟩
      have hac : a ≠ c := by
        intro e
        subst c
        have hbd : b = d := by
          cases x with
          | inl x =>
            have h1 := hux.2
            have h2 := hvx.2
            dsimp [Incidence] at h1 h2
            linear_combination h1 - h2
          | inr x =>
            cases y with
            | inl y =>
              have h1 := huy.2
              have h2 := hvy.2
              dsimp [Incidence] at h1 h2
              linear_combination h1 - h2
            | inr y =>
              exact False.elim (hxy (congrArg Sum.inr (hux.2.symm.trans huy.2)))
        exact huv (by simp [hbd])
      cases x with
      | inl x =>
        rcases x with ⟨s,t⟩
        cases y with
        | inl y =>
          rcases y with ⟨z,w⟩
          have h1 := hux.2
          have h2 := hvx.2
          have h3 := huy.2
          have h4 := hvy.2
          dsimp [Incidence] at h1 h2 h3 h4
          have hp : (a-c)*(s-z) = 0 := by
            linear_combination -h1 + h2 + h3 - h4
          have hsz : s = z := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hac))
          have htw : t = w := by rw [hsz] at h1; linear_combination h1 - h3
          simp [hsz, htw]
        | inr y => exact False.elim (hac (huy.2.trans hvy.2.symm))
      | inr x => exact False.elim (hac (hux.2.trans hvx.2.symm))
    | inr v =>
      cases x with
      | inl x =>
        rcases x with ⟨s,t⟩
        cases y with
        | inl y =>
          rcases y with ⟨z,w⟩
          have hs : s = v := hvx.2
          have hz : z = v := hvy.2
          have h1 := hux.2
          have h2 := huy.2
          dsimp [Incidence] at h1 h2
          have htw : t = w := by rw [hs] at h1; rw [hz] at h2; linear_combination h1 - h2
          simp [hs, hz, htw]
        | inr y => exact False.elim hvy.2
      | inr x => exact False.elim hvx.2
  | inr u =>
    cases v with
    | inl v =>
      cases x with
      | inl x =>
        rcases x with ⟨s,t⟩
        cases y with
        | inl y =>
          rcases y with ⟨z,w⟩
          have hs : s = u := hux.2
          have hz : z = u := huy.2
          have h1 := hvx.2
          have h2 := hvy.2
          dsimp [Incidence] at h1 h2
          have htw : t = w := by rw [hs] at h1; rw [hz] at h2; linear_combination h1 - h2
          simp [hs, hz, htw]
        | inr y => exact False.elim huy.2
      | inr x => exact False.elim hux.2
    | inr v =>
      cases x with
      | inl x => exact False.elim (huv (congrArg Sum.inr (hux.2.symm.trans hvx.2)))
      | inr x => exact False.elim hux.2

theorem noC4 : ¬ HasC4 (graph F) := by
  rintro ⟨a,b,c,d,hac,hbd,hab,hbc,hcd,hda⟩
  exact hbd (common_neighbor_unique F a c b d hac hab hbc.symm hda.symm hcd)

/-- Replace a would-be self-neighbor by the corresponding direction point. -/
noncomputable def neighbor (u : Vertex F) (t : F) : Vertex F := by
  classical
  exact match u with
    | .inl (a,b) => if (t, a*t-b) = (a,b) then .inr a else .inl (t,a*t-b)
    | .inr a => .inl (a,t)

theorem neighbor_adj (u : Vertex F) (t : F) : (graph F).Adj u (neighbor F u t) := by
  classical
  cases u with
  | inl u =>
    rcases u with ⟨a,b⟩
    by_cases h : (t,a*t-b) = (a,b)
    · simp [neighbor, h, graph, Incidence]
    · simp only [neighbor, h, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simpa only [ne_eq, Sum.inl.injEq, eq_comm] using h
      · dsimp [Incidence]
        ring
  | inr a => simp [neighbor, graph, Incidence]

theorem neighbor_injective (u : Vertex F) : Function.Injective (neighbor F u) := by
  classical
  intro t s hts
  cases u with
  | inl u =>
    rcases u with ⟨a,b⟩
    by_cases ht : (t,a*t-b) = (a,b)
    · by_cases hs : (s,a*s-b) = (a,b)
      · exact (congrArg Prod.fst ht).trans (congrArg Prod.fst hs).symm
      · simp [neighbor, ht, hs] at hts
    · by_cases hs : (s,a*s-b) = (a,b)
      · simp [neighbor, ht, hs] at hts
      · have hp : (t, a*t-b) = (s, a*s-b) := by
          simpa only [neighbor, ht, hs, ↓reduceIte, Sum.inl.injEq] using hts
        exact congrArg Prod.fst hp
  | inr a => simpa [neighbor] using hts

variable [Fintype F]

noncomputable instance : DecidableRel (graph F).Adj := Classical.decRel _

omit [Field F] in
theorem card_vertex : Fintype.card (Vertex F) = Fintype.card F ^ 2 + Fintype.card F := by
  simp [Vertex, pow_two]

theorem minimum_degree (u : Vertex F) : Fintype.card F ≤ (graph F).degree u := by
  classical
  let e : F ↪ (graph F).neighborSet u :=
    ⟨fun t => ⟨neighbor F u t, neighbor_adj F u t⟩,
      fun t s h => neighbor_injective F u (congrArg Subtype.val h)⟩
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_embedding e

theorem noStar_compl : ¬ HasStar (graph F)ᶜ (Fintype.card F ^ 2) := by
  classical
  rw [hasStar_iff_degree]
  push Not
  intro u
  have h := minimum_degree F u
  have hq : 0 < Fintype.card F := Fintype.card_pos
  rw [SimpleGraph.degree_compl, card_vertex]
  have hq2 : 0 < Fintype.card F ^ 2 := pow_pos hq _
  omega

/-- The construction rules out a Ramsey bound on q² + q vertices. -/
theorem not_ramseyBound :
    ¬ RamseyBound (Fintype.card F ^ 2) (Fintype.card F ^ 2 + Fintype.card F) := by
  classical
  let e : Fin (Fintype.card F ^ 2 + Fintype.card F) ≃ Vertex F :=
    (finCongr (card_vertex F).symm).trans (Fintype.equivFin (Vertex F)).symm
  intro h
  rcases h ((graph F).comap e) with hc | hs
  · apply noC4 F
    rcases hc with ⟨a,b,c,d,hac,hbd,hab,hbc,hcd,hda⟩
    exact ⟨e a, e b, e c, e d, e.injective.ne hac, e.injective.ne hbd,
      hab, hbc, hcd, hda⟩
  · apply noStar_compl F
    rcases hs with ⟨v,f,hf⟩
    refine ⟨e v, f.trans e.toEmbedding, ?_⟩
    intro i
    exact ⟨e.injective.ne (hf i).1, (hf i).2⟩

theorem lower_bound :
    Fintype.card F ^ 2 + Fintype.card F + 1 ≤ c4StarRamsey (Fintype.card F ^ 2) :=
  c4StarRamsey_lower (not_ramseyBound F)

/-- Exact square parameter for any finite field of even order. -/
theorem exact_even (heven : Fintype.card F % 2 = 0) :
    c4StarRamsey (Fintype.card F ^ 2) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  have hl := lower_bound F
  have hu := c4StarRamsey_le_of_bound
    (ramsey_bound_even_square (Fintype.card F) Fintype.card_pos heven)
  omega

end PolarityFamily

/-- The classical infinite family, with q = 2^r and r positive. -/
theorem c4StarRamsey_power_two (r : ℕ) (hr : 0 < r) :
    c4StarRamsey ((2 ^ r) ^ 2) = (2 ^ r) ^ 2 + 2 ^ r + 1 := by
  classical
  let : Fintype (GaloisField 2 r) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 r) = 2 ^ r := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 r (by omega)
  have heven : Fintype.card (GaloisField 2 r) % 2 = 0 := by
    rw [hc]
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    simp [pow_succ]
  simpa only [hc] using PolarityFamily.exact_even (GaloisField 2 r) heven

theorem c4StarRamsey_sixty_four : c4StarRamsey 64 = 73 := by
  simpa using c4StarRamsey_power_two 3 (by omega)

theorem c4StarRamsey_256 : c4StarRamsey 256 = 273 := by
  simpa using c4StarRamsey_power_two 4 (by omega)

end JSP000443
