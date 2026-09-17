import JSP000947

namespace JSP000947

theorem force3 (n : ℕ) (hn : 7 < n) (hg : Good n) : 3 ∣ n := by
  apply forced_divisor 3 7 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩

theorem force5 (n : ℕ) (hn : 21 < n) (hg : Good n) : 5 ∣ n := by
  apply forced_divisor 5 21 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨4, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩

theorem force11 (n : ℕ) (hn : 1035 < n) (hg : Good n) : 11 ∣ n := by
  apply forced_divisor 11 1035 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨10, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨8, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨4, by decide, by decide, by decide⟩
  · exact ⟨9, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨6, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩

theorem force13 (n : ℕ) (hn : 4109 < n) (hg : Good n) : 13 ∣ n := by
  apply forced_divisor 13 4109 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨12, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨4, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨9, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩
  · exact ⟨11, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨8, by decide, by decide, by decide⟩
  · exact ⟨10, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨6, by decide, by decide, by decide⟩

theorem force19 (n : ℕ) (hn : 262163 < n) (hg : Good n) : 19 ∣ n := by
  apply forced_divisor 19 262163 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨13, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨16, by decide, by decide, by decide⟩
  · exact ⟨14, by decide, by decide, by decide⟩
  · exact ⟨6, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨8, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨12, by decide, by decide, by decide⟩
  · exact ⟨15, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨11, by decide, by decide, by decide⟩
  · exact ⟨4, by decide, by decide, by decide⟩
  · exact ⟨10, by decide, by decide, by decide⟩
  · exact ⟨9, by decide, by decide, by decide⟩

theorem force29 (n : ℕ) (hn : 268435485 < n) (hg : Good n) : 29 ∣ n := by
  apply forced_divisor 29 268435485 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨28, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨22, by decide, by decide, by decide⟩
  · exact ⟨6, by decide, by decide, by decide⟩
  · exact ⟨12, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨10, by decide, by decide, by decide⟩
  · exact ⟨23, by decide, by decide, by decide⟩
  · exact ⟨25, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨13, by decide, by decide, by decide⟩
  · exact ⟨27, by decide, by decide, by decide⟩
  · exact ⟨4, by decide, by decide, by decide⟩
  · exact ⟨21, by decide, by decide, by decide⟩
  · exact ⟨11, by decide, by decide, by decide⟩
  · exact ⟨9, by decide, by decide, by decide⟩
  · exact ⟨24, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨26, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨8, by decide, by decide, by decide⟩
  · exact ⟨16, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨15, by decide, by decide, by decide⟩
  · exact ⟨14, by decide, by decide, by decide⟩

theorem force37 (n : ℕ) (hn : 68719476773 < n) (hg : Good n) : 37 ∣ n := by
  apply forced_divisor 37 68719476773 n (by decide) _ hn hg
  intro r hr hzero
  interval_cases r
  · omega
  · exact ⟨36, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨26, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨23, by decide, by decide, by decide⟩
  · exact ⟨27, by decide, by decide, by decide⟩
  · exact ⟨32, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨16, by decide, by decide, by decide⟩
  · exact ⟨24, by decide, by decide, by decide⟩
  · exact ⟨30, by decide, by decide, by decide⟩
  · exact ⟨28, by decide, by decide, by decide⟩
  · exact ⟨11, by decide, by decide, by decide⟩
  · exact ⟨33, by decide, by decide, by decide⟩
  · exact ⟨13, by decide, by decide, by decide⟩
  · exact ⟨4, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨35, by decide, by decide, by decide⟩
  · exact ⟨25, by decide, by decide, by decide⟩
  · exact ⟨22, by decide, by decide, by decide⟩
  · exact ⟨31, by decide, by decide, by decide⟩
  · exact ⟨15, by decide, by decide, by decide⟩
  · exact ⟨29, by decide, by decide, by decide⟩
  · exact ⟨10, by decide, by decide, by decide⟩
  · exact ⟨12, by decide, by decide, by decide⟩
  · exact ⟨6, by decide, by decide, by decide⟩
  · exact ⟨34, by decide, by decide, by decide⟩
  · exact ⟨21, by decide, by decide, by decide⟩
  · exact ⟨14, by decide, by decide, by decide⟩
  · exact ⟨9, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨8, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩

theorem known_good (n : ℕ) (hn : n ∈ known) : Good n := by
  have checked : ∀ n ∈ known, 2 < n ∧ n ≤ 105 ∧
      ∀ k ∈ Finset.Icc 1 6, 2 ^ k < n → (n - 2 ^ k).Prime := by decide
  obtain ⟨hn2, hn105, htests⟩ := checked n hn
  refine ⟨hn2, ?_⟩
  intro k hk hpow
  have hk6 : k ≤ 6 := by
    by_contra! hlarge
    have ht := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlarge
    have : 128 ≤ 2 ^ k := by simpa using ht
    omega
  exact htests k (Finset.mem_Icc.mpr ⟨hk, hk6⟩) hpow

theorem small_classification (n : ℕ) (hn : n ≤ 21) (hg : Good n) : n ∈ known := by
  have h1 := hg.2 1 (by decide)
  have h2 := hg.2 2 (by decide)
  have h3 := hg.2 3 (by decide)
  have h4 := hg.2 4 (by decide)
  have h0 := hg.1
  interval_cases n <;> norm_num [known] at *

end JSP000947
