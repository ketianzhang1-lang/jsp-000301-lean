import JSP000554Complete

namespace Verify554
open Filter
open scoped Topology

-- Use Mathlib's genuine prime enumeration and least prime factor directly.
def RoughGap (n : ℕ) : Prop :=
  ∃ m : ℕ, Nat.nth Nat.Prime n < m ∧ m < Nat.nth Nat.Prime (n + 1) ∧
    Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n ≤ m.minFac

noncomputable def goodCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter RoughGap).card

noncomputable def badCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => ¬ RoughGap n).card

theorem consecutive_primes (n : ℕ) :
    (Nat.nth Nat.Prime n).Prime ∧ (Nat.nth Nat.Prime (n + 1)).Prime ∧
      Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) ∧
      ∀ m : ℕ, Nat.nth Nat.Prime n < m →
        m < Nat.nth Nat.Prime (n + 1) → ¬ m.Prime := by
  exact ⟨Erdos682.nthPrime_prime n, Erdos682.nthPrime_prime (n + 1),
    Erdos682.nthPrime_lt_succ n, Erdos682.no_prime_between_nthPrime n⟩

theorem actual_least_prime_factor (m : ℕ) (hm : 1 < m) :
    m.minFac.Prime ∧ m.minFac ∣ m ∧
      ∀ q : ℕ, q.Prime → q ∣ m → m.minFac ≤ q := by
  refine ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, ?_⟩
  intro q hq hd
  exact Nat.minFac_le_of_dvd hq.two_le hd

theorem good_predicate_iff (n : ℕ) :
    RoughGap n ↔ n ∈ JSP000554.goodGapIndices := by
  exact (JSP000554.mem_goodGapIndices_iff n).symm

theorem bad_predicate_iff (n : ℕ) :
    (¬ RoughGap n) ↔
      JSP000554.BadGap (Nat.nth Nat.Prime n)
        (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n) := by
  exact (JSP000554.badGap_iff_exceptional n).symm

theorem density_one_literal_count :
    Tendsto (fun N : ℕ => (goodCount N : ℝ) / N) atTop (𝓝 1) := by
  have hcount (N : ℕ) :
      goodCount N = Erdos682.prefixCount JSP000554.goodGapIndices N := by
    classical
    unfold goodCount Erdos682.prefixCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro n _
    exact good_predicate_iff n
  have hfun : (fun N : ℕ => (goodCount N : ℝ) / N) =
      (fun N : ℕ => (Erdos682.prefixCount JSP000554.goodGapIndices N : ℝ) / N) := by
    funext N
    rw [hcount N]
  rw [hfun]
  exact JSP000554.goodGap_count_ratio_tendsto

theorem density_zero_literal_count :
    Tendsto (fun N : ℕ => (badCount N : ℝ) / N) atTop (𝓝 0) := by
  have hcount (N : ℕ) :
      badCount N = Erdos682.prefixCount JSP000554.badGapIndices N := by
    classical
    unfold badCount Erdos682.prefixCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro n _
    exact bad_predicate_iff n
  have hfun : (fun N : ℕ => (badCount N : ℝ) / N) =
      (fun N : ℕ => (Erdos682.prefixCount JSP000554.badGapIndices N : ℝ) / N) := by
    funext N
    rw [hcount N]
  rw [hfun]
  exact JSP000554.badGap_count_ratio_tendsto

theorem residue_equivalence_with_prime_endpoints (p h : ℕ) (hh : 2 ≤ h) :
    (p.Prime ∧ (p + h).Prime ∧
      (∀ m : ℕ, p < m → m < p + h → ¬ m.Prime) ∧
      ∀ m : ℕ, p < m → m < p + h → m.minFac < h) ↔
    h ≤ p ∧ p.Prime ∧ (p + h).Prime ∧
      p % JSP000554.primorial h ∈ JSP000554.omegaSet h := by
  exact JSP000554.badGap_iff_residue_all hh

end Verify554
