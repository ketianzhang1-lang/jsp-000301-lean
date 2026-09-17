import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
The algebraic core of the classical Bose--Chowla construction.
Mathematical credit: R. C. Bose and S. Chowla (1962/63).
This implementation was prepared with OpenAI ChatGPT assistance.
-/

namespace BoseChowla

open Polynomial

theorem product_injective
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (θ : K) (h : ℕ) (hh : 0 < h) (hθ : (minpoly F θ).natDegree = h)
    (s t : Multiset F) (hs : s.card = h) (ht : t.card = h)
    (heq : (s.map (fun a => θ - algebraMap F K a)).prod =
      (t.map (fun a => θ - algebraMap F K a)).prod) : s = t := by
  let P : F[X] := (s.map (fun a => X - C a)).prod
  let Q : F[X] := (t.map (fun a => X - C a)).prod
  have hP : P.Monic := monic_multisetProd_X_sub_C s
  have hQ : Q.Monic := monic_multisetProd_X_sub_C t
  have hdP : P.natDegree = h := by simpa [P] using hs
  have hdQ : Q.natDegree = h := by simpa [Q] using ht
  have hdeg : (P - Q).degree < P.degree :=
    degree_sub_lt_left (by rw [degree_eq_natDegree hP.ne_zero,
      degree_eq_natDegree hQ.ne_zero, hdP, hdQ])
      hP.ne_zero (hP.leadingCoeff.trans hQ.leadingCoeff.symm)
  have heval : aeval θ (P - Q) = 0 := by
    simp only [map_sub, P, Q, map_multiset_prod, Multiset.map_map,
      Function.comp_def, aeval_X, aeval_C]
    exact sub_eq_zero.mpr heq
  have hzero : P - Q = 0 := by
    by_contra hn
    have hd := minpoly.degree_le_of_ne_zero F θ hn heval
    have hm : (minpoly F θ) ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at hθ
      omega
    rw [degree_eq_natDegree hm, hθ] at hd
    rw [degree_eq_natDegree hP.ne_zero, hdP] at hdeg
    exact (not_lt_of_ge hd) hdeg
  have he := congrArg Polynomial.roots (sub_eq_zero.mp hzero)
  simpa [P, Q, roots_multiset_prod_X_sub_C] using he

theorem sub_ne_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (θ : K) (hθ : 2 ≤ (minpoly F θ).natDegree) (a : F) :
    θ - algebraMap F K a ≠ 0 := by
  intro he
  have ht := sub_eq_zero.mp he
  rw [ht, minpoly.eq_X_sub_C, natDegree_X_sub_C] at hθ
  omega

theorem exists_exponent_family (p h : ℕ) [Fact p.Prime] (hh : 2 ≤ h) :
    ∃ e : ZMod p → ℕ, Function.Injective e ∧
      (∀ a, e a < p ^ h - 1) ∧
      ∀ s t : Multiset (ZMod p), s.card = h → t.card = h →
        (s.map e).sum = (t.map e).sum → s = t := by
  classical
  let K := GaloisField p h
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) K
  have hdegree : (minpoly (ZMod p) θ).natDegree = h := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) θ).mp hθ]
    exact GaloisField.finrank p (by omega)
  have hne (a : ZMod p) : θ - algebraMap (ZMod p) K a ≠ 0 :=
    sub_ne_zero θ (by omega) a
  let u (a : ZMod p) : Kˣ := Units.mk0 _ (hne a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  have hex (a : ZMod p) : ∃ n : ℕ, g ^ n = u a := hg (u a)
  choose n hn using hex
  let e (a : ZMod p) := n a % Nat.card Kˣ
  have hc : Nat.card Kˣ = p ^ h - 1 := by
    rw [Nat.card_units, GaloisField.card p h (by omega)]
  have he (a : ZMod p) : (g : K) ^ e a = θ - algebraMap (ZMod p) K a := by
    have hx : g ^ e a = u a := (pow_mod_natCard g (n a)).trans (hn a)
    exact congrArg Units.val hx
  have hei : Function.Injective e := by
    intro a b hab
    have hx : θ - algebraMap (ZMod p) K a = θ - algebraMap (ZMod p) K b := by
      rw [← he a, ← he b, hab]
    exact (algebraMap (ZMod p) K).injective (sub_right_inj.mp hx)
  refine ⟨e, hei, ?_, ?_⟩
  · intro a
    rw [← hc]
    exact Nat.mod_lt _ Nat.card_pos
  · intro s t hs ht hsum
    have hprod (v : Multiset (ZMod p)) :
        (g : K) ^ (v.map e).sum =
          (v.map (fun a => θ - algebraMap (ZMod p) K a)).prod := by
      induction v using Multiset.induction_on with
      | empty => simp
      | @cons a v ih => simp [pow_add, he, ih]
    apply product_injective θ h (by omega) hdegree s t hs ht
    rw [← hprod s, ← hprod t, hsum]

/-- Equal sums of `h` members, allowing repetitions, have the same multiset of terms. -/
def IsBh (h : ℕ) (A : Finset ℕ) : Prop :=
  ∀ s t : Multiset ℕ, s.card = h → t.card = h →
    (∀ a ∈ s, a ∈ A) → (∀ a ∈ t, a ∈ A) → s.sum = t.sum → s = t

private theorem lift_multiset {α β : Type*} (f : α → β) (s : Multiset β)
    (hs : ∀ x ∈ s, ∃ a, f a = x) : ∃ t : Multiset α, t.map f = s := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, rfl⟩
  | @cons x s ih =>
    obtain ⟨a, ha⟩ := hs x (Multiset.mem_cons_self _ _)
    obtain ⟨t, ht⟩ := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    exact ⟨a ::ₘ t, by simp [ha, ht]⟩

private theorem sum_shift {α : Type*} (e : α → ℕ) (s : Multiset α) :
    (s.map (fun a => e a + 1)).sum = (s.map e).sum + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons,
      Multiset.card_cons, ih]; omega

/-- The finite Bose--Chowla lower-bound construction, for every prime and every `h ≥ 2`.
The conclusion is stronger than uniqueness only for sums of distinct elements. -/
theorem exists_bose_chowla (p h : ℕ) (hp : p.Prime) (hh : 2 ≤ h) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p ^ h - 1) ∧ A.card = p ∧ IsBh h A := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, hei, heB, heS⟩ := exists_exponent_family p h hh
  let f (a : ZMod p) := e a + 1
  have hfi : Function.Injective f := by
    intro a b hab
    apply hei
    exact Nat.add_right_cancel hab
  let A := Finset.univ.image f
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    have ha := heB a
    simp only [Finset.mem_Icc, f]
    omega
  · rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, ZMod.card]
  · intro s t hs ht hsA htA hsum
    have hlift (v : Multiset ℕ) (hv : ∀ a ∈ v, a ∈ A) :
        ∃ w : Multiset (ZMod p), w.map f = v := by
      apply lift_multiset
      intro x hx
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hv x hx)
      exact ⟨a, ha⟩
    obtain ⟨s', rfl⟩ := hlift s hsA
    obtain ⟨t', rfl⟩ := hlift t htA
    have hs' : s'.card = h := by simpa using hs
    have ht' : t'.card = h := by simpa using ht
    have heq : (s'.map e).sum = (t'.map e).sum := by
      change (s'.map (fun a => e a + 1)).sum =
        (t'.map (fun a => e a + 1)).sum at hsum
      rw [sum_shift, sum_shift, hs', ht'] at hsum
      omega
    exact congrArg (Multiset.map f) (heS s' t' hs' ht' heq)

/-- JSP-000212: the finite cubic lower-bound construction. -/
theorem jsp000212 (p : ℕ) (hp : p.Prime) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p ^ 3 - 1) ∧ A.card = p ∧
      ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = 3 → T.card = 3 →
        S.sum id = T.sum id → S = T := by
  obtain ⟨A, hA, hc, hB⟩ := exists_bose_chowla p 3 hp (by decide)
  refine ⟨A, hA, hc, ?_⟩
  intro S T hS hT hcS hcT hsum
  apply Finset.val_injective
  apply hB S.val T.val hcS hcT hS hT
  simpa using hsum

end BoseChowla
