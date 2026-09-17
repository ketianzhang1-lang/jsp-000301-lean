import JSP912.Grid

namespace JSP912

/-- The product of all precision levels up to `K`. -/
def partialProd (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | K + 1 => partialProd r K * gridProd (2 ^ (K + 1)) r

/-- A deliberately generous, explicit exponent for the binary anchor. -/
def anchorExponent (r K : ℕ) : ℕ := 16 * r * (r + 1) * (K + 1) * 2 ^ K

def candidate (r K : ℕ) : ℕ := 2 ^ anchorExponent r K * partialProd r K

def scaleConstant (r : ℕ) : ℕ := 16 * r * (r + 1) + 2

lemma two_pow_pos (i : ℕ) : 0 < (2 : ℕ) ^ i := by positivity

lemma one_le_two_pow (i : ℕ) : 1 ≤ (2 : ℕ) ^ i := two_pow_pos i

lemma succ_le_two_pow (i : ℕ) : i + 1 ≤ (2 : ℕ) ^ i := by
  induction i with
  | zero => norm_num
  | succ i ih => rw [pow_succ]; omega

lemma le_two_pow (i : ℕ) : i ≤ (2 : ℕ) ^ i := by
  have h := succ_le_two_pow i
  omega

lemma gridProd_dyadic_bound (i r : ℕ) :
    gridProd (2 ^ i) r ≤ 2 ^ (2 * 2 ^ i * (i * r * (r + 1) + r)) := by
  induction r with
  | zero => simp [gridProd]
  | succ r ih =>
    let u : ℕ := i * (r + 1)
    have ha1 : 1 ≤ (2 : ℕ) ^ u := one_le_two_pow u
    have hb : (2 : ℕ) ^ u * (2 ^ u + 1) ≤ 2 ^ (u * 2 + 1) := by
      calc
        (2 : ℕ) ^ u * (2 ^ u + 1) ≤ 2 ^ u * (2 * 2 ^ u) := by nlinarith
        _ = 2 ^ (u * 2 + 1) := by rw [pow_add, pow_mul]; norm_num; ring
    calc
      gridProd (2 ^ i) (r + 1) = gridProd (2 ^ i) r *
          (2 ^ u * (2 ^ u + 1)) ^ (2 * 2 ^ i) := by
            simp only [gridProd, ← pow_mul, u]
      _ ≤ 2 ^ (2 * 2 ^ i * (i * r * (r + 1) + r)) *
          (2 ^ (u * 2 + 1)) ^ (2 * 2 ^ i) :=
            Nat.mul_le_mul ih (Nat.pow_le_pow_left hb _)
      _ = 2 ^ (2 * 2 ^ i * (i * (r + 1) * (r + 1 + 1) + (r + 1))) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            dsimp [u]
            ring

lemma gridProd_dyadic_bound_simple (i r : ℕ) (hi : 1 ≤ i) :
    gridProd (2 ^ i) r ≤ 2 ^ (4 * i * 2 ^ i * r * (r + 1)) := by
  apply le_trans (gridProd_dyadic_bound i r)
  apply Nat.pow_le_pow_right (by omega)
  have hh : r ≤ i * r * (r + 1) := by
    have h1 : r ≤ i * r := by nlinarith
    have h2 : i * r ≤ i * r * (r + 1) := by nlinarith
    omega
  nlinarith [Nat.mul_le_mul_left (2 * 2 ^ i) hh]

lemma partialProd_pos (r K : ℕ) : 0 < partialProd r K := by
  induction K with
  | zero => simp [partialProd]
  | succ K ih => exact Nat.mul_pos ih (gridProd_pos (two_pow_pos _) r)

lemma partialProd_bound (r K : ℕ) : partialProd r K ≤ 2 ^ anchorExponent r K := by
  induction K with
  | zero => simpa [partialProd] using (one_le_two_pow (anchorExponent r 0))
  | succ K ih =>
    calc
      partialProd r (K + 1) = partialProd r K * gridProd (2 ^ (K + 1)) r := rfl
      _ ≤ 2 ^ anchorExponent r K * 2 ^ (4 * (K + 1) * 2 ^ (K + 1) * r * (r + 1)) :=
        Nat.mul_le_mul ih (gridProd_dyadic_bound_simple (K + 1) r (by omega))
      _ = 2 ^ (anchorExponent r K + 4 * (K + 1) * 2 ^ (K + 1) * r * (r + 1)) :=
        (pow_add _ _ _).symm
      _ ≤ 2 ^ anchorExponent r (K + 1) := by
        apply Nat.pow_le_pow_right (by omega)
        simp only [anchorExponent, pow_succ]
        ring_nf
        omega

lemma level_dvd_partialProd (r i K : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K) :
    gridProd (2 ^ i) r ∣ partialProd r K := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases he : i = K + 1
    · subst i
      exact dvd_mul_left _ _
    · have hik : i ≤ K := by omega
      exact dvd_mul_of_dvd_left (ih hik) _

lemma anchor_dvd (r K : ℕ) : 2 ^ anchorExponent r K ∣ candidate r K := by
  exact dvd_mul_right _ _

lemma level_with_anchor_dvd (r i K : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K) :
    2 ^ anchorExponent r K * gridProd (2 ^ i) r ∣ candidate r K := by
  exact mul_dvd_mul_left _ (level_dvd_partialProd r i K hi hiK)

lemma candidate_pos (r K : ℕ) : 0 < candidate r K :=
  Nat.mul_pos (two_pow_pos _) (partialProd_pos r K)

lemma index_le_anchorExponent (r K : ℕ) (hr : 1 ≤ r) : K ≤ anchorExponent r K := by
  have hc : 1 ≤ 16 * r * (r + 1) := by nlinarith
  have hp := one_le_two_pow K
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_right (K + 1) hc) hp
  dsimp [anchorExponent]
  nlinarith

lemma index_le_candidate (r K : ℕ) (hr : 1 ≤ r) : K ≤ candidate r K := by
  calc
    K ≤ 2 ^ K := le_two_pow K
    _ ≤ 2 ^ anchorExponent r K := Nat.pow_le_pow_right (by omega) (index_le_anchorExponent r K hr)
    _ ≤ candidate r K := by
      have hh : 1 ≤ partialProd r K := partialProd_pos r K
      dsimp [candidate]
      nlinarith [two_pow_pos (anchorExponent r K)]

lemma baseProd_dyadic_eq (i r : ℕ) :
    baseProd (2 ^ i) r = 2 ^ (r * (r + 1) * i * 2 ^ i) := by
  rw [baseProd_eq, ← pow_mul]
  congr 1
  ring

lemma anchorExponent_le_scale (r K : ℕ) :
    1 + anchorExponent r K ≤ scaleConstant r * 4 ^ K := by
  have hh := succ_le_two_pow K
  have h4 : (4 : ℕ) ^ K = 2 ^ K * 2 ^ K := by
    rw [← mul_pow]
    norm_num
  have hp := one_le_two_pow K
  dsimp [anchorExponent, scaleConstant]
  rw [h4]
  have hmul := Nat.mul_le_mul_right (16 * r * (r + 1) * 2 ^ K) hh
  nlinarith [Nat.mul_le_mul hp hp]

lemma dyadic_level_gap (r K i a b : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K)
    (hab : Consecutive (candidate r K) a b)
    (haA : ((2 : ℝ) ^ (r * (r + 1) * i * 2 ^ i)) ≤ a)
    (hbE : (b : ℝ) ≤ (2 : ℝ) ^ anchorExponent r K) :
    (b : ℝ) / a - 1 ≤ 1 / (2 : ℝ) ^ (r * i) := by
  have hm : 2 ≤ (2 : ℕ) ^ i := by
    have hh := Nat.pow_le_pow_right (show (1 : ℕ) ≤ 2 by omega) hi
    simpa using hh
  have hh := grid_consecutive_gap (2 ^ i) r (anchorExponent r K) (candidate r K) a b hm
    (level_with_anchor_dvd r i K hi hiK) hab
    (by simpa only [baseProd_dyadic_eq, Nat.cast_pow, Nat.cast_ofNat] using haA) hbE
  simpa only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm i r] using hh

end JSP912
