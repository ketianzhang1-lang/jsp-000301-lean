import BoseChowla

/-!
The full finite Bose--Chowla construction for prime powers and modular sums.
Mathematical credit: R. C. Bose and S. Chowla (1962/63), Theorem 1.
This supplement was prepared with OpenAI ChatGPT assistance.
-/

namespace BoseChowlaPrimePower

open Polynomial

/-- The finite-field construction with equality of sums modulo the multiplicative order. -/
theorem exponent_family
    (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h : ℕ) (hh : 2 ≤ h) (hdim : Module.finrank F K = h) :
    ∃ e : F → ℕ, Function.Injective e ∧
      (∀ a, e a < Nat.card K - 1) ∧
      ∀ s t : Multiset F, s.card = h → t.card = h →
        Nat.ModEq (Nat.card K - 1) (s.map e).sum (t.map e).sum → s = t := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element_of_finite_top F K
  have hdegree : (minpoly F θ).natDegree = h :=
    ((Field.primitive_element_iff_minpoly_natDegree_eq F θ).mp hθ).trans hdim
  have hne (a : F) : θ - algebraMap F K a ≠ 0 :=
    BoseChowla.sub_ne_zero θ (by omega) a
  let u (a : F) : Kˣ := Units.mk0 _ (hne a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  have hex (a : F) : ∃ n : ℕ, g ^ n = u a := hg (u a)
  choose n hn using hex
  let e (a : F) := n a % Nat.card Kˣ
  have hc : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have he (a : F) : (g : K) ^ e a = θ - algebraMap F K a := by
    have hx : g ^ e a = u a := (pow_mod_natCard g (n a)).trans (hn a)
    exact congrArg Units.val hx
  have hei : Function.Injective e := by
    intro a b hab
    have hx : θ - algebraMap F K a = θ - algebraMap F K b := by
      rw [← he a, ← he b, hab]
    exact (algebraMap F K).injective (sub_right_inj.mp hx)
  refine ⟨e, hei, ?_, ?_⟩
  · intro a
    rw [← hc]
    exact Nat.mod_lt _ Nat.card_pos
  · intro s t hs ht hsum
    have hprod (v : Multiset F) :
        (g : K) ^ (v.map e).sum =
          (v.map (fun a => θ - algebraMap F K a)).prod := by
      induction v using Multiset.induction_on with
      | empty => simp
      | @cons a v ih => simp [pow_add, he, ih]
    rw [← hc] at hsum
    have hp : g ^ (s.map e).sum = g ^ (t.map e).sum := calc
      g ^ (s.map e).sum = g ^ ((s.map e).sum % Nat.card Kˣ) :=
        (pow_mod_natCard g _).symm
      _ = g ^ ((t.map e).sum % Nat.card Kˣ) := congrArg (g ^ ·) hsum
      _ = g ^ (t.map e).sum := pow_mod_natCard g _
    apply BoseChowla.product_injective θ h (by omega) hdegree s t hs ht
    rw [← hprod s, ← hprod t]
    exact congrArg Units.val hp

/-- Exponents for every prime-power base field, without assuming an extension exists. -/
theorem prime_power_exponents (p r h : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hh : 2 ≤ h) :
    ∃ e : GaloisField p r → ℕ, Function.Injective e ∧
      (∀ a, e a < (p ^ r) ^ h - 1) ∧
      ∀ s t : Multiset (GaloisField p r), s.card = h → t.card = h →
        Nat.ModEq ((p ^ r) ^ h - 1) (s.map e).sum (t.map e).sum → s = t := by
  let F := GaloisField p r
  let K := GaloisField p (r * h)
  have hrank : Module.finrank (ZMod p) F = r := GaloisField.finrank p (by omega)
  have hrankK : Module.finrank (ZMod p) K = r * h :=
    GaloisField.finrank p (by positivity)
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := F) (L := K) (by rw [hrank, hrankK]; exact dvd_mul_right r h)
  algebraize [f.toRingHom]
  have hdim : Module.finrank F K = h := by
    have ht := Module.finrank_mul_finrank (ZMod p) F K
    rw [hrank, hrankK] at ht
    exact Nat.eq_of_mul_eq_mul_left hr ht
  have hcard : Nat.card K = (p ^ r) ^ h := by
    rw [GaloisField.card p (r * h) (by positivity), pow_mul]
  simpa only [hcard] using exponent_family F K h hh hdim

/-- Equality of h-term sums modulo m determines the entire multiset, including repetitions. -/
def IsBhMod (h m : ℕ) (A : Finset ℕ) : Prop :=
  ∀ s t : Multiset ℕ, s.card = h → t.card = h →
    (∀ a ∈ s, a ∈ A) → (∀ a ∈ t, a ∈ A) → Nat.ModEq m s.sum t.sum → s = t

theorem IsBhMod.isBh {h m : ℕ} {A : Finset ℕ} (hA : IsBhMod h m A) :
    BoseChowla.IsBh h A := by
  intro s t hs ht hsA htA heq
  apply hA s t hs ht hsA htA
  rw [heq]

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

/-- Bose--Chowla for every prime power p^r, with full modular uniqueness. -/
theorem exists_prime_power_modular (p r h : ℕ) (hp : p.Prime)
    (hr : 0 < r) (hh : 2 ≤ h) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 ((p ^ r) ^ h - 1) ∧
      A.card = p ^ r ∧ IsBhMod h ((p ^ r) ^ h - 1) A := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype (GaloisField p r) := Fintype.ofFinite _
  obtain ⟨e, hei, heB, heS⟩ := prime_power_exponents p r h hr hh
  let f (a : GaloisField p r) := e a + 1
  have hfi : Function.Injective f := by
    intro a b hab
    exact hei (Nat.add_right_cancel hab)
  let A := Finset.univ.image f
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    have ha := heB a
    simp only [Finset.mem_Icc, f]
    omega
  · rw [Finset.card_image_of_injective _ hfi, Finset.card_univ,
      Fintype.card_eq_nat_card, GaloisField.card p r (by omega)]
  · intro s t hs ht hsA htA hsum
    have hlift (v : Multiset ℕ) (hv : ∀ a ∈ v, a ∈ A) :
        ∃ w : Multiset (GaloisField p r), w.map f = v := by
      apply lift_multiset
      intro x hx
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hv x hx)
      exact ⟨a, ha⟩
    obtain ⟨s', rfl⟩ := hlift s hsA
    obtain ⟨t', rfl⟩ := hlift t htA
    have hs' : s'.card = h := by simpa using hs
    have ht' : t'.card = h := by simpa using ht
    have heq : Nat.ModEq ((p ^ r) ^ h - 1) (s'.map e).sum (t'.map e).sum := by
      change Nat.ModEq _ (s'.map (fun a => e a + 1)).sum
        (t'.map (fun a => e a + 1)).sum at hsum
      rw [sum_shift, sum_shift, hs', ht'] at hsum
      exact Nat.ModEq.add_right_cancel' h hsum
    exact congrArg (Multiset.map f) (heS s' t' hs' ht' heq)

/-- The original catalog condition now at every prime-power cardinality. -/
theorem jsp000212_prime_power (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 ((p ^ r) ^ 3 - 1) ∧ A.card = p ^ r ∧
      ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = 3 → T.card = 3 →
        S.sum id = T.sum id → S = T := by
  obtain ⟨A, hA, hc, hB⟩ := exists_prime_power_modular p r 3 hp hr (by decide)
  refine ⟨A, hA, hc, ?_⟩
  intro S T hS hT hcS hcT hsum
  apply Finset.val_injective
  apply hB.isBh S.val T.val hcS hcT hS hT
  simpa using hsum

end BoseChowlaPrimePower
