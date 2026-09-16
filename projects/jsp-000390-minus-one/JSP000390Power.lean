import JSP000390
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.FieldTheory.Finite.Basic

/-!
# JSP-000390 / Erdős 479: all positive power-of-two residues

This supplements the known k=-1 result with the known infinite parameter family
k=2^i, i>=1. It does not resolve the original question for arbitrary k different
from 1. Mathematical credit remains with Graham, D. H. Lehmer and E. Lehmer;
Quanyu Tang's public note explains the n=i*p construction.

The implementation replaces prime-power bookkeeping with a finite-monoid
pigeonhole argument and uses Mathlib's elementary infinitude of primes congruent
to one. It proves the useful general-base lemma as well, without claiming a new
mathematical discovery. Prepared with OpenAI ChatGPT assistance.
-/

namespace JSP000390Power

/-- An equality of two powers propagates to a periodic tail. -/
lemma power_tail_periodic {M : Type*} [Monoid M] (x : M)
    {u v N : ℕ} (huv : u < v) (hv : v ≤ N) (heq : x ^ u = x ^ v) :
    ∀ t : ℕ, x ^ (N + (v - u) * t) = x ^ N := by
  have hu : u ≤ N := by omega
  have hstep : x ^ (N + (v - u)) = x ^ N := by
    calc
      x ^ (N + (v - u)) = x ^ (v + (N - u)) := by congr 1; omega
      _ = x ^ v * x ^ (N - u) := by rw [pow_add]
      _ = x ^ u * x ^ (N - u) := by rw [← heq]
      _ = x ^ (u + (N - u)) := by rw [pow_add]
      _ = x ^ N := by congr 1; omega
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, pow_add, ih, ← pow_add, hstep]

/-- There is a positive period for powers modulo i, starting no later than i.
This does not assume that a is invertible modulo i. -/
lemma exists_zmod_power_period (a : ℤ) (i : ℕ) (hi : 0 < i) :
    ∃ d : ℕ, 0 < d ∧ ∀ t : ℕ,
      (a : ZMod i) ^ (i + d * t) = (a : ZMod i) ^ i := by
  let : NeZero i := ⟨by omega⟩
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin (i + 1) => (a : ZMod i) ^ j.val) (by simp [ZMod.card])
  have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨v.val - u.val, Nat.sub_pos_of_lt hlt,
      power_tail_periodic (a : ZMod i) hlt (by omega) heq⟩
  · exact ⟨u.val - v.val, Nat.sub_pos_of_lt hgt,
      power_tail_periodic (a : ZMod i) hgt (by omega) heq.symm⟩

/-- For every integer base and positive exponent i, a suitable prime p gives
an arbitrarily large solution n=i*p with residue a^i. -/
theorem power_residue_unbounded (a : ℤ) (i : ℕ) (hi : 0 < i) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ 0 < n ∧ a ^ n ≡ a ^ i [ZMOD (n : ℤ)] := by
  obtain ⟨d, hd, hperiod⟩ := exists_zmod_power_period a i hi
  obtain ⟨p, hp, hlarge, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (max B i) (Nat.ne_of_gt hd)
  have hip : i < p := lt_of_le_of_lt (le_max_right B i) hlarge
  have hBp : B < p := lt_of_le_of_lt (le_max_left B i) hlarge
  have hcop : i.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hi hip)).symm
  obtain ⟨t, ht⟩ := hmod.symm.dvd'
  have hpform : p = 1 + d * t := by omega
  have hexp : i * p = i + d * (i * t) := by rw [hpform]; ring
  have hzi : (a : ZMod i) ^ (i * p) = (a : ZMod i) ^ i := by
    rw [hexp]
    exact hperiod (i * t)
  have hci : a ^ (i * p) ≡ a ^ i [ZMOD (i : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simpa only [Int.cast_pow] using hzi
  have : Fact p.Prime := ⟨hp⟩
  have hzp : (a : ZMod p) ^ (i * p) = (a : ZMod p) ^ i := by
    rw [Nat.mul_comm i p, pow_mul, ZMod.pow_card]
  have hcp : a ^ (i * p) ≡ a ^ i [ZMOD (p : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simpa only [Int.cast_pow] using hzp
  have hcopz : (i : ℤ).natAbs.Coprime (p : ℤ).natAbs := by simpa using hcop
  have hboth := (Int.modEq_and_modEq_iff_modEq_mul hcopz).mp ⟨hci, hcp⟩
  refine ⟨i * p, ?_, Nat.mul_pos hi hp.pos, ?_⟩
  · nlinarith
  · simpa only [Nat.cast_mul] using hboth

/-- Infinitely many positive solutions, uniformly for every positive exponent. -/
theorem power_residue_infinite (a : ℤ) (i : ℕ) (hi : 0 < i) :
    {n : ℕ | 0 < n ∧ a ^ n ≡ a ^ i [ZMOD (n : ℤ)]}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro B
  obtain ⟨n, hn, hpos, hcong⟩ := power_residue_unbounded a i hi B
  exact ⟨n, ⟨hpos, hcong⟩, hn⟩

/-- The complete known power-of-two family in the same positive-modulus predicate
as the earlier k=-1 submission. -/
theorem powers_of_two_infinite (i : ℕ) (hi : 0 < i) :
    (JSP000390.Solutions ((2 : ℤ) ^ i)).Infinite :=
  power_residue_infinite 2 i hi

/-- The unbounded-set form matching the corresponding original-question slice. -/
theorem powers_of_two_infinite_unrestricted (i : ℕ) (hi : 0 < i) :
    {n : ℕ | (2 : ℤ) ^ n ≡ (2 : ℤ) ^ i [ZMOD (n : ℤ)]}.Infinite :=
  (powers_of_two_infinite i hi).mono (fun _ hn => hn.2)

/-- Both known families proved in the combined submission; no claim for other k. -/
theorem combined_known_families :
    (JSP000390.Solutions (-1)).Infinite ∧
    ∀ i : ℕ, 0 < i → (JSP000390.Solutions ((2 : ℤ) ^ i)).Infinite :=
  ⟨JSP000390.minus_one_infinite, powers_of_two_infinite⟩

end JSP000390Power
