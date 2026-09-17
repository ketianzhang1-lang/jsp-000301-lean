import Core
namespace JSP000780General

lemma monomial_strict {r x y K j k c d : ℕ}
    (hy : 0 < y) (hxy : K*y < x) (_hK : 0 < K)
    (hjk : j < k) (hkr : k ≤ r) (hc : 0 < c) (hd : d ≤ K) :
    d*x^(r-k)*y^k < c*x^(r-j)*y^j := by
  have hx : 0 < x := by omega
  have he : 0 < k-j := by omega
  have hp : K ≤ K^(k-j) := Nat.le_self_pow (by omega) K
  have hg : K*y^(k-j) < x^(k-j) := by
    calc
      _ ≤ K^(k-j)*y^(k-j) := Nat.mul_le_mul_right _ hp
      _ = (K*y)^(k-j) := (mul_pow ..).symm
      _ < _ := Nat.pow_lt_pow_left hxy (by omega)
  have hfactor : 0 < x^(r-k)*y^j := by positivity
  calc
    d*x^(r-k)*y^k = (d*y^(k-j))*(x^(r-k)*y^j) := by
      have heq : y^k = y^j * y^(k-j) := by
        rw [← pow_add]; congr 1; omega
      rw [heq]; ring
    _ ≤ (K*y^(k-j))*(x^(r-k)*y^j) := by gcongr
    _ < x^(k-j)*(x^(r-k)*y^j) := Nat.mul_lt_mul_of_pos_right hg hfactor
    _ ≤ c*(x^(k-j)*(x^(r-k)*y^j)) := Nat.le_mul_of_pos_left _ hc
    _ = c*x^(r-j)*y^j := by
      rw [show r-j = (r-k)+(k-j) by omega, pow_add]; ring

lemma monomial_bound {r x y K j c : ℕ} (hxy : y ≤ x)
    (hj : 0 < j) (hjr : j ≤ r) (hc : c ≤ K) :
    c*x^(r-j)*y^j ≤ K*x^(r-1)*y := by
  have hpow : y^(j-1) ≤ x^(j-1) := Nat.pow_le_pow_left hxy _
  calc
    c*x^(r-j)*y^j = c*x^(r-j)*y^(j-1)*y := by
      have heq : y^j = y^(j-1)*y := by
        rw [← pow_succ]; congr 1; omega
      rw [heq]; ring
    _ ≤ K*x^(r-j)*x^(j-1)*y := by gcongr
    _ = K*x^(r-1)*y := by
      rw [show r-1 = (r-j)+(j-1) by omega, pow_add]; ring

lemma first_dominates {r x y K : ℕ} (hr : 0 < r) (hxy : 2^r*K*y < x)
    (h2 : 2*y ≤ x) : K*x^(r-1)*y < (x-y)^r := by
  have hx : 0 < x := by omega
  have hsmall : 2^r*(K*x^(r-1)*y) < x^r := by
    calc
      _ = (2^r*K*y)*x^(r-1) := by ring
      _ < x*x^(r-1) := Nat.mul_lt_mul_of_pos_right hxy (by positivity)
      _ = x^r := by
        rw [mul_comm, ← pow_succ]; congr 1; omega
  have hlarge : x^r ≤ 2^r*(x-y)^r := by
    calc
      _ ≤ (2*(x-y))^r := Nat.pow_le_pow_left (by omega) r
      _ = _ := mul_pow ..
  exact Nat.lt_of_mul_lt_mul_left (hsmall.trans_le hlarge)

end JSP000780General
