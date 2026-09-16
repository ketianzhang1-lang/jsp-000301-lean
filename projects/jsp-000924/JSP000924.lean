import Mathlib

/-!
# JSP-000924 / Erdos 1113: an infinite fourth-power Sierpinski family

The mathematics is Izotov's partial-cover plus Sophie Germain construction,
with the explicit progression in Filaseta--Finch--Kozek (2008), Section 2.
This independently written, AI-assisted formalization does NOT prove that any
member has no finite prime covering set, and does not settle the open problem.
-/
namespace JSP000924

/-- A standard Sierpinski number, including exponent zero. -/
def Sierpinski (k : ℕ) : Prop :=
  0 < k ∧ Odd k ∧ ∀ n : ℕ, ¬ Nat.Prime (k * 2 ^ n + 1)

/-- The product 2*3*5*17*257*65537*641*6700417. -/
def modulus : ℕ := 36893488147419103230

/-- The explicit residue in the 2008 paper, not a newly discovered witness. -/
def seed : ℕ := 734110615000775

def root (j : ℕ) : ℕ := seed + modulus * j

def member (j : ℕ) : ℕ := (root j) ^ 4

/-- The six fixed divisors used outside n = 2 modulo 4. -/
def selectedDivisor (r : ℕ) : ℕ :=
  if r % 2 = 1 then 3 else
  if r % 8 = 4 then 17 else
  if r % 16 = 8 then 257 else
  if r % 32 = 16 then 65537 else
  if r = 32 then 641 else 6700417

/-- Exact finite arithmetic certificate. The arbitrary exponent is reduced to
this table by a separately proved periodicity theorem, not by finite testing. -/
lemma finite_cover : ∀ r : Fin 64, r.val % 4 ≠ 2 →
    1 < selectedDivisor r.val ∧ selectedDivisor r.val ≤ 6700417 ∧
    2 ^ 64 % selectedDivisor r.val = 1 ∧
    modulus % selectedDivisor r.val = 0 ∧
    (seed ^ 4 * 2 ^ r.val + 1) % selectedDivisor r.val = 0 := by
  decide

lemma pow_remainder (p n : ℕ) (hp : 2 ^ 64 % p = 1) (hp1 : 1 < p) :
    2 ^ n % p = 2 ^ (n % 64) % p := by
  have h : Nat.ModEq p (2 ^ 64) 1 := by
    change 2 ^ 64 % p = 1 % p
    rw [Nat.mod_eq_of_lt hp1]
    exact hp
  change Nat.ModEq p (2 ^ n) (2 ^ (n % 64))
  conv_lhs => rw [← Nat.div_add_mod n 64, pow_add, pow_mul]
  calc
    (2 ^ 64) ^ (n / 64) * 2 ^ (n % 64) ≡
        1 ^ (n / 64) * 2 ^ (n % 64) [MOD p] := (h.pow _).mul_right _
    _ = 2 ^ (n % 64) := by rw [one_pow, one_mul]

lemma root_mod (j p : ℕ) (hp : modulus % p = 0) :
    root j % p = seed % p := by
  simp [root, Nat.add_mod, Nat.mul_mod, hp]

lemma member_mod (j p : ℕ) (hp : modulus % p = 0) :
    member j % p = seed ^ 4 % p :=
  (show Nat.ModEq p (root j) seed from root_mod j p hp).pow 4

lemma root_large (j : ℕ) : 6700417 < root j := by
  dsimp [root, seed, modulus]
  omega

lemma root_le_member (j : ℕ) : root j ≤ member j := by
  have h := root_large j
  have hs : root j ≤ (root j) ^ 2 := by nlinarith
  have ht : (root j) ^ 2 ≤ ((root j) ^ 2) ^ 2 := by nlinarith
  dsimp [member]
  nlinarith [hs, ht]

lemma member_odd (j : ℕ) : Odd (member j) := by
  have h : Odd (root j) := by
    refine ⟨367055307500387 + 18446744073709551615 * j, ?_⟩
    dsimp [root, seed, modulus]
    ring
  exact h.pow

/-- The algebraic part of the construction: an actual proper natural divisor. -/
theorem sophie_germain_proper_divisor (x : ℕ) (hx : 2 ≤ x) :
    ∃ d : ℕ, 1 < d ∧ d < 4 * x ^ 4 + 1 ∧ d ∣ 4 * x ^ 4 + 1 := by
  let d := 2 * x ^ 2 - 2 * x + 1
  let e := 2 * x ^ 2 + 2 * x + 1
  have hxx : 2 * x ≤ x ^ 2 := by nlinarith
  have hle : 2 * x ≤ 2 * x ^ 2 := by omega
  have hsub := Nat.sub_add_cancel hle
  have hd : 1 < d := by dsimp [d]; nlinarith
  have he : 1 < e := by dsimp [e]; nlinarith
  have hid : d * e = 4 * x ^ 4 + 1 := by
    have hz : ((d : ℕ) : ℤ) = 2 * (x : ℤ) ^ 2 - 2 * x + 1 := by
      dsimp [d]
      push_cast [Nat.cast_sub hle]
      ring
    have hi : (2 * (x : ℤ) ^ 2 - 2 * x + 1) *
        (2 * (x : ℤ) ^ 2 + 2 * x + 1) = 4 * (x : ℤ) ^ 4 + 1 := by ring
    rw [← hz] at hi
    dsimp [e]
    exact_mod_cast hi
  refine ⟨d, hd, ?_, ⟨e, hid.symm⟩⟩
  nlinarith

/-- Every term has a proper divisor. This is quantified over every progression
parameter and every exponent, including n=0. -/
theorem family_proper_divisor (j n : ℕ) :
    ∃ d : ℕ, 1 < d ∧ d < member j * 2 ^ n + 1 ∧ d ∣ member j * 2 ^ n + 1 := by
  by_cases hn : n % 4 = 2
  · have heq : n = 4 * (n / 4) + 2 := by omega
    have hpow : 0 < 2 ^ (n / 4) := by positivity
    have hx : 2 ≤ root j * 2 ^ (n / 4) := by
      have h := root_large j
      nlinarith
    have hidentity : member j * 2 ^ n + 1 = 4 * (root j * 2 ^ (n / 4)) ^ 4 + 1 := by
      dsimp [member]
      conv_lhs => rw [heq, pow_add]
      have he : (2 : ℕ) ^ (4 * (n / 4)) = (2 ^ (n / 4)) ^ 4 := by
        rw [mul_comm, pow_mul]
      rw [he, mul_pow]
      norm_num
      ring
    rw [hidentity]
    exact sophie_germain_proper_divisor _ hx
  · let r : Fin 64 := ⟨n % 64, Nat.mod_lt _ (by decide)⟩
    have hr : r.val % 4 ≠ 2 := by
      simpa [r, Nat.mod_mod_of_dvd n (by decide : 4 ∣ 64)] using hn
    obtain ⟨hlo, hhi, hperiod, hM, hzero⟩ := finite_cover r hr
    let p := selectedDivisor r.val
    have hm : Nat.ModEq p (member j) (seed ^ 4) := member_mod j p hM
    have hp : Nat.ModEq p (2 ^ n) (2 ^ r.val) := pow_remainder p n hperiod hlo
    have hz : (member j * 2 ^ n + 1) % p = 0 := by
      calc
        (member j * 2 ^ n + 1) % p = (seed ^ 4 * 2 ^ r.val + 1) % p :=
          (hm.mul hp).add_right 1
        _ = 0 := hzero
    have hpow : 0 < 2 ^ n := by positivity
    have hlarge := root_large j
    have hquart := root_le_member j
    exact ⟨p, hlo, by nlinarith, Nat.dvd_of_mod_eq_zero hz⟩

/-- The complete explicit fourth-power family recorded in FFK Section 2. -/
theorem family_sierpinski (j : ℕ) : Sierpinski (member j) := by
  refine ⟨by have h := root_large j; have h' := root_le_member j; omega,
    member_odd j, ?_⟩
  intro n hp
  obtain ⟨d, hd, hlt, hdiv⟩ := family_proper_divisor j n
  rcases (Nat.dvd_prime hp).mp hdiv with h | h <;> omega

/-- The familiar concrete candidate itself is Sierpinski. No claim concerning
arbitrary finite prime covers is made here. -/
theorem candidate_sierpinski : Sierpinski (734110615000775 ^ 4) := by
  simpa [member, root, seed] using family_sierpinski 0

/-- There are genuinely infinitely many distinct fourth-power Sierpinski numbers. -/
theorem infinitely_many_fourth_powers :
    {k : ℕ | Sierpinski k ∧ ∃ t : ℕ, k = t ^ 4}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  refine ⟨member (B + 1), ⟨family_sierpinski _, ⟨root (B + 1), rfl⟩⟩, ?_⟩
  have hb : B < root (B + 1) := by dsimp [root, seed, modulus]; omega
  exact hb.trans_le (root_le_member (B + 1))

/-- Only this particular classical prime list, NOT every finite list. -/
def standardPrimes : Finset ℕ := {3, 5, 17, 257, 65537, 641, 6700417}

lemma standard_arithmetic (p : ℕ) (hp : p ∈ standardPrimes) :
    modulus % p = 0 ∧ (seed ^ 4 * 2 ^ 2 + 1) % p ≠ 0 := by
  simp only [standardPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [modulus, seed]

/-- The standard seven-prime list fails to cover each member, already at n=2.
This must not be confused with the open no-finite-cover statement. -/
theorem standard_list_not_cover (j : ℕ) :
    ¬ (∀ n : ℕ, ∃ p ∈ standardPrimes, p ∣ member j * 2 ^ n + 1) := by
  intro h
  obtain ⟨p, hp, hd⟩ := h 2
  obtain ⟨hM, hnonzero⟩ := standard_arithmetic p hp
  have hm : Nat.ModEq p (member j) (seed ^ 4) := member_mod j p hM
  have hc : (member j * 2 ^ 2 + 1) % p = (seed ^ 4 * 2 ^ 2 + 1) % p :=
    (hm.mul_right (2 ^ 2)).add_right 1
  exact hnonzero (hc.symm.trans (Nat.mod_eq_zero_of_dvd hd))

end JSP000924
