import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max

/-!
An explicit universal lower bound for inclusion-maximal Sidon subsets of [1,N].
This is a lower-bound component of JSP-000154 / Erdos 156, not the open upper bound.
-/

namespace JSP000154
open Finset
open scoped BigOperators

/-- Pair sums are unique up to interchanging the summands; repetitions are allowed. -/
def Sidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Inclusion-maximal among Sidon subsets of the positive interval. -/
def MaximalSidon (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Icc 1 N ∧ Sidon A ∧
  ∀ x ∈ Icc 1 N, x ∉ A → ¬ Sidon (insert x A)

def lePairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 ≤ p.2

def ltPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 < p.2

theorem choose_two_identity (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem lePairs_eq (A : Finset ℕ) : lePairs A = ltPairs A ∪ A.diag := by
  ext p
  simp only [lePairs, ltPairs, mem_filter, mem_product, mem_union, mem_diag]
  grind

theorem lePairs_card (A : Finset ℕ) :
    2 * (lePairs A).card = A.card ^ 2 + A.card := by
  rw [lePairs_eq, card_union_of_disjoint]
  · rw [ltPairs, card_product_filter_lt, diag_card]
    nlinarith [choose_two_identity A.card]
  · rw [disjoint_left]
    intro p hp hd
    simp only [ltPairs, mem_filter, mem_product, mem_diag] at hp hd
    omega

theorem ltPairs_card (A : Finset ℕ) :
    2 * (ltPairs A).card + A.card = A.card ^ 2 := by
  rw [ltPairs, card_product_filter_lt]
  exact choose_two_identity A.card

/-- Inserting a new element fails exactly through a double or a three-term relation. -/
theorem insertion_obstruction {A : Finset ℕ} (hA : Sidon A) {x : ℕ}
    (hx : x ∉ A) (hbad : ¬ Sidon (insert x A)) :
    (∃ a ∈ A, ∃ b ∈ A, a < b ∧ 2*x = a+b) ∨
    (∃ c ∈ A, ∃ a ∈ A.erase c, ∃ b ∈ A.erase c, a ≤ b ∧ x+c = a+b) := by
  classical
  by_contra! h
  apply hbad
  intro a ha b hb c hc d hd heq
  simp only [mem_insert] at ha hb hc hd
  have hdouble : ∀ a ∈ A, ∀ b ∈ A, 2*x ≠ a+b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hab' | hab' | hab'
    · exact h.1 a ha b hb hab' hab
    · subst b
      have : x = a := by omega
      exact hx (this ▸ ha)
    · exact h.1 b hb a ha hab' (by omega)
  have htriple : ∀ c ∈ A, ∀ a ∈ A, ∀ b ∈ A, x+c ≠ a+b := by
    intro c hc a ha b hb he
    have hac : a ≠ c := by
      intro h
      subst a
      have hxb : x = b := by omega
      exact hx (hxb ▸ hb)
    have hbc : b ≠ c := by
      intro h
      subst b
      have hxa : x = a := by omega
      exact hx (hxa ▸ ha)
    have hae : a ∈ A.erase c := mem_erase.mpr ⟨hac, ha⟩
    have hbe : b ∈ A.erase c := mem_erase.mpr ⟨hbc, hb⟩
    rcases le_total a b with hab | hba
    · exact h.2 c hc a hae b hbe hab he
    · exact h.2 c hc b hbe a hae hba (by omega)
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;>
    rcases hc with rfl | hc <;> rcases hd with rfl | hd
  all_goals grind [Sidon]

/-- Candidate values excluded by a relation x+c=a+b, with c different from both summands. -/
def tripleBlocks (A : Finset ℕ) : Finset ℕ :=
  A.biUnion fun c => (lePairs (A.erase c)).image fun p => p.1 + p.2 - c

/-- Candidate values excluded by a relation 2x=a+b, with distinct summands. -/
def midpointBlocks (A : Finset ℕ) : Finset ℕ :=
  (ltPairs A).image fun p => (p.1 + p.2) / 2

theorem interval_covered {A : Finset ℕ} {N : ℕ} (hA : MaximalSidon A N) :
    Icc 1 N ⊆ A ∪ tripleBlocks A ∪ midpointBlocks A := by
  intro x hx
  by_cases hxa : x ∈ A
  · exact mem_union_left _ (mem_union_left _ hxa)
  · rcases insertion_obstruction hA.2.1 hxa (hA.2.2 x hx hxa) with h | h
    · obtain ⟨a, ha, b, hb, hab, heq⟩ := h
      apply mem_union_right
      apply mem_image.mpr
      exact ⟨(a,b), mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩, by omega⟩
    · obtain ⟨c, hc, a, ha, b, hb, hab, heq⟩ := h
      apply mem_union_left
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨c, hc, ?_⟩
      apply mem_image.mpr
      exact ⟨(a,b), mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩, by omega⟩

theorem tripleBlocks_card (A : Finset ℕ) :
    2 * (tripleBlocks A).card ≤
      A.card * ((A.card - 1)^2 + (A.card - 1)) := by
  have hcard : (tripleBlocks A).card ≤ ∑ c ∈ A, (lePairs (A.erase c)).card := by
    apply (card_biUnion_le).trans
    exact sum_le_sum fun c hc => card_image_le
  calc
    2 * (tripleBlocks A).card ≤ 2 * ∑ c ∈ A, (lePairs (A.erase c)).card :=
      Nat.mul_le_mul_left 2 hcard
    _ = ∑ c ∈ A, (2 * (lePairs (A.erase c)).card) := mul_sum _ _ _
    _ = ∑ _c ∈ A, ((A.card - 1)^2 + (A.card - 1)) := by
      apply sum_congr rfl
      intro c hc
      rw [lePairs_card, card_erase_of_mem hc]
    _ = A.card * ((A.card - 1)^2 + (A.card - 1)) := by simp

theorem midpointBlocks_card (A : Finset ℕ) :
    2 * (midpointBlocks A).card + A.card ≤ A.card ^ 2 := by
  have hcard : (midpointBlocks A).card ≤ (ltPairs A).card := card_image_le
  nlinarith [ltPairs_card A]

/-- The all-N explicit cubic obstruction bound for every inclusion-maximal Sidon set. -/
theorem maximal_sidon_lower_bound {A : Finset ℕ} {N : ℕ}
    (hA : MaximalSidon A N) : 2 * N ≤ A.card ^ 3 + A.card := by
  have hcover : N ≤ A.card + (tripleBlocks A).card + (midpointBlocks A).card := by
    calc
      N = (Icc 1 N).card := by simp
      _ ≤ (A ∪ tripleBlocks A ∪ midpointBlocks A).card := card_le_card (interval_covered hA)
      _ ≤ (A ∪ tripleBlocks A).card + (midpointBlocks A).card := card_union_le _ _
      _ ≤ A.card + (tripleBlocks A).card + (midpointBlocks A).card :=
        Nat.add_le_add_right (card_union_le _ _) _
  have ht := tripleBlocks_card A
  have hm := midpointBlocks_card A
  cases he : A.card with
  | zero =>
    simp only [he] at hcover ht hm
    norm_num at ht hm ⊢
    simpa [ht, hm] using hcover
  | succ k =>
    rw [he] at hcover ht hm
    simp only [Nat.succ_sub_one] at ht
    nlinarith

/-- In particular, the cardinality is at least the real cube-root scale. -/
theorem interval_le_card_cube {A : Finset ℕ} {N : ℕ}
    (hA : MaximalSidon A N) : N ≤ A.card ^ 3 := by
  have h := maximal_sidon_lower_bound hA
  have hm : A.card ≤ A.card ^ 3 := Nat.le_self_pow (by decide : 3 ≠ 0) _
  omega

theorem cube_root_lower_bound {A : Finset ℕ} {N : ℕ}
    (hA : MaximalSidon A N) : (N : ℝ) ^ (1 / 3 : ℝ) ≤ A.card := by
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num : (0:ℝ)<3)).mpr
  norm_cast
  exact interval_le_card_cube hA

/-- A maximal Sidon set exists even for the empty interval N=0. -/
theorem exists_maximal_sidon (N : ℕ) : ∃ A : Finset ℕ, MaximalSidon A N := by
  classical
  let F := ((Icc 1 N).powerset).filter Sidon
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [F, Sidon]
  obtain ⟨A, hAF, hmax⟩ := exists_max_image F card hF
  have hA : A ⊆ Icc 1 N ∧ Sidon A := by simpa [F] using hAF
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro x hx hxa hinsert
  have hiF : insert x A ∈ F := by
    simp only [F, mem_filter, mem_powerset]
    exact ⟨insert_subset hx hA.1, hinsert⟩
  have hc := hmax (insert x A) hiF
  rw [card_insert_of_notMem hxa] at hc
  omega

/-- The actual minimum over inclusion-maximal Sidon sets, with existence proved above. -/
noncomputable def minimumSize (N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℕ, MaximalSidon A N ∧ A.card = m}

theorem minimumSize_attained (N : ℕ) :
    ∃ A : Finset ℕ, MaximalSidon A N ∧ A.card = minimumSize N := by
  have hn : {m : ℕ | ∃ A : Finset ℕ, MaximalSidon A N ∧ A.card = m}.Nonempty := by
    obtain ⟨A, hA⟩ := exists_maximal_sidon N
    exact ⟨A.card, A, hA, rfl⟩
  exact Nat.sInf_mem hn

/-- The bound applies to the minimum extremal function, not just a chosen construction. -/
theorem minimumSize_lower_bound (N : ℕ) : 2 * N ≤ minimumSize N ^ 3 + minimumSize N := by
  obtain ⟨A, hA, he⟩ := minimumSize_attained N
  simpa [he] using maximal_sidon_lower_bound hA

theorem minimumSize_cube_root (N : ℕ) :
    (N : ℝ) ^ (1 / 3 : ℝ) ≤ minimumSize N := by
  obtain ⟨A, hA, he⟩ := minimumSize_attained N
  simpa [he] using cube_root_lower_bound hA

theorem sidon_subset {A B : Finset ℕ} (hB : Sidon B) (hAB : A ⊆ B) :
    Sidon A := by
  intro a ha b hb c hc d hd he
  exact hB a (hAB ha) b (hAB hb) c (hAB hc) d (hAB hd) he

/-- The one-element definition is exactly inclusion-maximality, rather than
maximum cardinality or maximality within a restricted family. -/
theorem maximal_iff_inclusion {A : Finset ℕ} {N : ℕ} :
    MaximalSidon A N ↔ A ⊆ Icc 1 N ∧ Sidon A ∧
      ∀ B : Finset ℕ, B ⊆ Icc 1 N → Sidon B → A ⊆ B → B = A := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro B hB hs hAB
    apply Subset.antisymm _ hAB
    intro x hx
    by_contra hxa
    exact h.2.2 x (hB hx) hxa (sidon_subset hs (insert_subset hx hAB))
  · rintro ⟨hA, hs, hmax⟩
    refine ⟨hA, hs, ?_⟩
    intro x hx hxa hsi
    have he := hmax (insert x A) (insert_subset hx hA) hsi (subset_insert _ _)
    exact hxa (he ▸ mem_insert_self x A)

/-- An explicit leading-constant form of the elementary lower bound. -/
theorem doubled_cube_root_lower_bound {A : Finset ℕ} {N : ℕ}
    (hA : MaximalSidon A N) :
    (2 * (N : ℝ)) ^ (1 / 3 : ℝ) ≤ (A.card : ℝ) + 1 := by
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 3)).mpr
  have h : 2 * (N : ℝ) ≤ (A.card : ℝ)^3 + A.card := by
    exact_mod_cast maximal_sidon_lower_bound hA
  have hm : (0 : ℝ) ≤ A.card := by positivity
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  nlinarith [sq_nonneg (A.card : ℝ)]

theorem minimumSize_doubled_cube_root (N : ℕ) :
    (2 * (N : ℝ)) ^ (1 / 3 : ℝ) ≤ (minimumSize N : ℝ) + 1 := by
  obtain ⟨A, hA, he⟩ := minimumSize_attained N
  simpa [he] using doubled_cube_root_lower_bound hA

end JSP000154
