import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

/-!
Mycielski's 1955 construction, independently formalized for the known upper-bound
component of JSP-000843 (Erdos 1013 / 1104).
Mathematical credit: Jan Mycielski, "Sur le coloriage des graphes",
Colloquium Mathematicum 3 (1955), 161-162.
Formalization prepared with OpenAI ChatGPT assistance. No new mathematics claimed.
-/
namespace JSP000843
open SimpleGraph

variable {V : Type*}

def LiftAdj (G : SimpleGraph V) : Option (V × Bool) → Option (V × Bool) → Prop
  | none, none => False
  | none, some (_, b) => b = true
  | some (_, b), none => b = true
  | some (v, b), some (w, c) => G.Adj v w ∧ (b = false ∨ c = false)

def mycielski (G : SimpleGraph V) : SimpleGraph (Option (V × Bool)) where
  Adj := LiftAdj G
  symm := ⟨by
    rintro (_ | ⟨v, b⟩) (_ | ⟨w, c⟩) <;>
      simp_all [LiftAdj, G.adj_comm, or_comm]⟩
  loopless := ⟨by
    rintro (_ | ⟨v, b⟩) <;> simp [LiftAdj]⟩

def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c⦄, G.Adj a b → G.Adj b c → G.Adj c a → False

theorem triangleFree_iff (G : SimpleGraph V) :
    TriangleFree G ↔ G.CliqueFree 3 := by
  classical
  constructor
  · intro h s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact h hab hbc hac.symm
  · intro h a b c hab hbc hca
    exact h {a,b,c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hca.symm,hbc⟩)

theorem mycielski_triangleFree {G : SimpleGraph V} (h : TriangleFree G) :
    TriangleFree (mycielski G) := by
  rintro (_ | ⟨a, ba⟩) (_ | ⟨b, bb⟩) (_ | ⟨c, bc⟩) <;>
    simp only [mycielski, LiftAdj]
  all_goals intro h1 h2 h3
  all_goals try simp_all
  all_goals exact h h1.1 h2.1 h3.1

theorem mycielski_colorable {G : SimpleGraph V} {n : ℕ} (h : G.Colorable n) :
    (mycielski G).Colorable (n + 1) := by
  obtain ⟨C⟩ := h
  let D : (mycielski G).Coloring (Option (Fin n)) :=
    Coloring.mk
      (fun x => match x with
        | none => none
        | some (v, _) => some (C v))
      (by
        rintro (_ | ⟨v,b⟩) (_ | ⟨w,c⟩) hadj <;>
          simp only [mycielski, LiftAdj] at hadj
        all_goals try simp
        all_goals exact fun he => C.valid hadj.1 he)
  simpa using D.colorable

/-- Delete the apex color after recoloring affected originals by their shadows. -/
theorem colorable_of_mycielski {G : SimpleGraph V} {n : ℕ}
    (h : (mycielski G).Colorable (n + 1)) : G.Colorable n := by
  classical
  obtain ⟨C⟩ := h
  let r : V → Fin (n + 1) := fun v =>
    if C (some (v,false)) = C none then C (some (v,true)) else C (some (v,false))
  have avoids (v : V) : r v ≠ C none := by
    dsimp [r]
    split_ifs with hv
    · exact C.valid (show (mycielski G).Adj (some (v,true)) none from rfl)
    · exact hv
  have valid {v w : V} (hvw : G.Adj v w) : r v ≠ r w := by
    have hoo : C (some (v,false)) ≠ C (some (w,false)) :=
      C.valid (show (mycielski G).Adj (some (v,false)) (some (w,false)) from ⟨hvw, Or.inl rfl⟩)
    have hso : C (some (v,true)) ≠ C (some (w,false)) :=
      C.valid (show (mycielski G).Adj (some (v,true)) (some (w,false)) from ⟨hvw, Or.inr rfl⟩)
    have hos : C (some (v,false)) ≠ C (some (w,true)) :=
      C.valid (show (mycielski G).Adj (some (v,false)) (some (w,true)) from ⟨hvw, Or.inl rfl⟩)
    dsimp [r]
    split_ifs with hv hw hw
    · exact (hoo (hv.trans hw.symm)).elim
    · exact hso
    · exact hos
    · exact hoo
  let D : G.Coloring {a : Fin (n + 1) // a ≠ C none} :=
    Coloring.mk (fun v => ⟨r v, avoids v⟩)
      (fun hadj he => valid hadj (congrArg Subtype.val he))
  simpa using D.colorable

@[reducible] def Vert : ℕ → Type
  | 0 => Fin 2
  | n + 1 => Option (Vert n × Bool)

instance vertFintype (n : ℕ) : Fintype (Vert n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 2))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Option (Vert n × Bool)))

def family : (n : ℕ) → SimpleGraph (Vert n)
  | 0 => ⊤
  | n + 1 => mycielski (family n)

theorem family_triangleFree (n : ℕ) : TriangleFree (family n) := by
  induction n with
  | zero =>
    intro a b c hab hbc hca
    have hab' : a ≠ b := hab
    have hbc' : b ≠ c := hbc
    have hca' : c ≠ a := hca
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  | succ n ih => exact mycielski_triangleFree ih

theorem family_cliqueFree (n : ℕ) : (family n).CliqueFree 3 :=
  (triangleFree_iff _).mp (family_triangleFree n)

theorem family_colorable (n : ℕ) : (family n).Colorable (n + 2) := by
  induction n with
  | zero =>
    change (⊤ : SimpleGraph (Fin 2)).Colorable 2
    exact ⟨(⊤ : SimpleGraph (Fin 2)).selfColoring⟩
  | succ n ih => exact mycielski_colorable ih

theorem family_not_colorable (n : ℕ) : ¬ (family n).Colorable (n + 1) := by
  induction n with
  | zero =>
    change ¬ (⊤ : SimpleGraph (Fin 2)).Colorable 1
    rintro ⟨C⟩
    exact C.valid (show (⊤ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) (1 : Fin 2) by decide)
      (Subsingleton.elim _ _)
  | succ n ih => exact fun h => ih (colorable_of_mycielski h)

theorem family_chromaticNumber (n : ℕ) :
    (family n).chromaticNumber = (n + 2 : ℕ) := by
  have h := (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable
    (G := family n) (n := n + 1)).mpr
    ⟨family_colorable n, family_not_colorable n⟩
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using h

theorem family_card_add_one (n : ℕ) :
    Fintype.card (Vert n) + 1 = 3 * 2 ^ n := by
  induction n with
  | zero => norm_num [Vert, vertFintype]
  | succ n ih =>
    change Fintype.card (Option (Vert n × Bool)) + 1 = _
    simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
    rw [pow_succ]
    omega

theorem family_card (n : ℕ) :
    Fintype.card (Vert n) = 3 * 2 ^ n - 1 := by
  have := family_card_add_one n
  omega

/-- The all-parameter known upper bound, with the standard Mathlib graph predicates. -/
theorem exists_triangleFree_exact_chromatic (n : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = 3 * 2 ^ n - 1 ∧ G.CliqueFree 3 ∧
      G.chromaticNumber = (n + 2 : ℕ) :=
  ⟨Vert n, vertFintype n, family n, family_card n,
    family_cliqueFree n, family_chromaticNumber n⟩

theorem exists_for_every_k (k : ℕ) (hk : 2 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = 3 * 2 ^ (k - 2) - 1 ∧ G.CliqueFree 3 ∧
      G.chromaticNumber = k := by
  have h := exists_triangleFree_exact_chromatic (k - 2)
  simpa only [Nat.sub_add_cancel hk] using h

end JSP000843
