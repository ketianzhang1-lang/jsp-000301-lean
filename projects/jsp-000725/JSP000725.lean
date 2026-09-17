import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Sqrt

/-! The classical consecutive-interval construction for JSP-000725.
This is a scoped formalization, not the eventual upper bound for arbitrary sets.
-/

namespace JSP000725
open Finset

def Admissible (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, ∀ T ⊆ A, (∑ x ∈ S, x) = (∑ x ∈ T, x) → S.card = T.card

theorem sum_lower (S : Finset ℕ) (a : ℕ) (ha : ∀ x ∈ S, a ≤ x) :
    S.card * (2*a + S.card) ≤ 2*(∑ x ∈ S, x) + S.card := by
  induction S using Finset.induction_on_min generalizing a with
  | empty => simp
  | insert b S hmin ih =>
    have hb : b ∉ S := fun h => Nat.lt_irrefl b (hmin b h)
    have hab := ha b (mem_insert_self b S)
    have hs := ih (b+1) (fun x hx => hmin x hx)
    simp only [card_insert_of_notMem hb, sum_insert hb]
    nlinarith

theorem sum_upper (S : Finset ℕ) (b : ℕ) (hb : ∀ x ∈ S, x ≤ b) :
    2*(∑ x ∈ S, x) + S.card*S.card ≤ S.card*(2*b+1) := by
  induction S using Finset.induction_on_max generalizing b with
  | empty => simp
  | insert a S hmax ih =>
    have ha : a ∉ S := fun h => Nat.lt_irrefl a (hmax a h)
    have hab := hb a (mem_insert_self a S)
    have hs := ih (a-1) (fun x hx => by have := hmax x hx; omega)
    simp only [card_insert_of_notMem ha, sum_insert ha]
    by_cases haz : a = 0
    · have he : S = ∅ := eq_empty_iff_forall_notMem.mpr (by
        intro x hx; have := hmax x hx; omega)
      simp [he, haz]
    · have : a-1+1 = a := by omega
      nlinarith

theorem interval_ordered_sums (N m : ℕ) (hm : m ≤ N)
    (hbound : (m+1)^2 ≤ 4*N+1)
    (S T : Finset ℕ) (hS : S ⊆ Icc (N-m+1) N)
    (hT : T ⊆ Icc (N-m+1) N) (hc : S.card < T.card) :
    (∑ x ∈ S, x) < (∑ x ∈ T, x) := by
  obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hc)
  have hlo := sum_lower U (N-m+1) (fun x hx => (mem_Icc.mp (hT (hUT hx))).1)
  have hup := sum_upper S N (fun x hx => (mem_Icc.mp (hS hx)).2)
  have hsum : (∑ x ∈ U, x) ≤ (∑ x ∈ T, x) := sum_le_sum_of_subset hUT
  rw [hU] at hlo
  have heq : N-m+m = N := Nat.sub_add_cancel hm
  have hsquare := sq_nonneg (2*(S.card : ℤ)+1-(m : ℤ))
  zify at hlo hup hsum heq hbound ⊢
  nlinarith

/-- Straus's top-interval construction, uniformly in its length and endpoint. -/
theorem interval_admissible (N m : ℕ) (hm : m ≤ N)
    (hbound : (m+1)^2 ≤ 4*N+1) : Admissible (Icc (N-m+1) N) := by
  intro S hS T hT hsum
  rcases lt_trichotomy S.card T.card with h | h | h
  · have := interval_ordered_sums N m hm hbound S T hS hT h
    omega
  · exact h
  · have := interval_ordered_sums N m hm hbound T S hT hS h
    omega

/-- The construction has the stated number of elements. -/
theorem interval_card (N m : ℕ) (hm : m ≤ N) :
    (Icc (N-m+1) N).card = m := by
  rw [Nat.card_Icc]
  omega

theorem length_le_endpoint {N m : ℕ} (h : (m+1)^2 ≤ 4*N+1) : m ≤ N := by
  by_contra hn
  have hn' : N+1 ≤ m := by omega
  have hs := sq_nonneg ((m : ℤ)-1)
  zify at h hn'
  nlinarith

/-- Explicit lower bound for every finite ambient interval, not just a subsequence. -/
theorem construction_for_every_N (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ Admissible A ∧
      A.card = Nat.sqrt (4*N+1)-1 := by
  let m := Nat.sqrt (4*N+1)-1
  have hs : 1 ≤ Nat.sqrt (4*N+1) := by
    rw [Nat.le_sqrt]; omega
  have hm1 : m+1 = Nat.sqrt (4*N+1) := by dsimp [m]; omega
  have hb : (m+1)^2 ≤ 4*N+1 := by rw [hm1]; exact Nat.sqrt_le' _
  have hm := length_le_endpoint hb
  refine ⟨Icc (N-m+1) N, ?_, interval_admissible N m hm hb, interval_card N m hm⟩
  intro x hx
  have := mem_Icc.mp hx
  exact mem_Icc.mpr ⟨by omega, this.2⟩

/-- A useful infinite family: 2t elements in [1,t²+t]. -/
theorem even_length_family (t : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (t^2+t) ∧ Admissible A ∧ A.card = 2*t := by
  have hb : (2*t+1)^2 ≤ 4*(t^2+t)+1 := by nlinarith
  have hm := length_le_endpoint hb
  refine ⟨Icc (t^2+t-2*t+1) (t^2+t), ?_,
    interval_admissible _ _ hm hb, interval_card _ _ hm⟩
  intro x hx
  have := mem_Icc.mp hx
  exact mem_Icc.mpr ⟨by omega, this.2⟩

theorem sum_block (a k : ℕ) :
    2*(∑ x ∈ Ico a (a+k), x)+k = k*(2*a+k) := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [sum_add_distrib]
  simp only [sum_const, card_range, smul_eq_mul]
  have hg := sum_range_id_mul_two k
  by_cases hk : k = 0
  · simp [hk]
  · have : k-1+1 = k := by omega
    nlinarith

/-- The all-t boundary obstruction: lowering the endpoint by one makes this
2t-element interval inadmissible. This does not assert a bound for arbitrary sets. -/
theorem boundary_obstruction (t : ℕ) (ht : 2 ≤ t) :
    ¬ Admissible (Icc (t^2-t) (t^2+t-1)) := by
  let S := Ico (t^2+1) (t^2+t)
  let T := Ico (t^2-t) (t^2)
  have htt : t ≤ t^2 := by nlinarith
  have hS : S ⊆ Icc (t^2-t) (t^2+t-1) := by
    intro x hx
    have := mem_Ico.mp hx
    apply mem_Icc.mpr; constructor <;> dsimp [S] at * <;> omega
  have hT : T ⊆ Icc (t^2-t) (t^2+t-1) := by
    intro x hx
    have := mem_Ico.mp hx
    apply mem_Icc.mpr; constructor <;> dsimp [T] at * <;> omega
  have hSc : S.card = t-1 := by dsimp [S]; rw [Nat.card_Ico]; omega
  have hTc : T.card = t := by dsimp [T]; rw [Nat.card_Ico]; omega
  have hs := sum_block (t^2+1) (t-1)
  have ht' := sum_block (t^2-t) t
  have heS : t^2+1+(t-1) = t^2+t := by omega
  have heT : t^2-t+t = t^2 := Nat.sub_add_cancel htt
  rw [heS] at hs
  rw [heT] at ht'
  have heq : (∑ x ∈ S, x) = (∑ x ∈ T, x) := by
    dsimp [S, T]
    have : t-1+1 = t := by omega
    nlinarith
  intro hA
  have := hA S hS T hT heq
  omega

end JSP000725
