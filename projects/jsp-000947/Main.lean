import Certificates
import Forced

namespace JSP000947

theorem case2 (n : ℕ) (hlow : 21 < n) (hhigh : n ≤ 1035)
    (hd : 15 ∣ n) (hg : Good n) : n ∈ known := by
  obtain ⟨t, rfl⟩ := hd
  have hchecked := checkTree_sound 7 2 certificate2 t (by omega) (by omega)
  exact passes_sound hchecked hhigh hg

theorem case3 (n : ℕ) (hlow : 1035 < n) (hhigh : n ≤ 4109)
    (hd : 165 ∣ n) (hg : Good n) : n ∈ known := by
  obtain ⟨t, rfl⟩ := hd
  have hchecked := checkTree_sound 5 7 certificate3 t (by omega) (by omega)
  exact passes_sound hchecked hhigh hg

theorem case4 (n : ℕ) (hlow : 4109 < n) (hhigh : n ≤ 262163)
    (hd : 2145 ∣ n) (hg : Good n) : n ∈ known := by
  obtain ⟨t, rfl⟩ := hd
  have hchecked := checkTree_sound 7 2 certificate4 t (by omega) (by omega)
  exact passes_sound hchecked hhigh hg

theorem case5 (n : ℕ) (hlow : 262163 < n) (hhigh : n ≤ 268435485)
    (hd : 40755 ∣ n) (hg : Good n) : n ∈ known := by
  obtain ⟨t, rfl⟩ := hd
  have hchecked := checkTree_sound 13 7 certificate5 t (by omega) (by omega)
  exact passes_sound hchecked hhigh hg

theorem case6 (n : ℕ) (hlow : 268435485 < n) (hhigh : n ≤ 68719476773)
    (hd : 1181895 ∣ n) (hg : Good n) : n ∈ known := by
  obtain ⟨t, rfl⟩ := hd
  have hchecked := checkTree_sound 16 228 certificate6 t (by omega) (by omega)
  exact passes_sound hchecked hhigh hg

theorem case7 (n : ℕ) (hlow : 68719476773 < n) (hhigh : n ≤ 17592186044416)
    (hd : 43730115 ∣ n) (hg : Good n) : n ∈ known := by
  obtain ⟨t, rfl⟩ := hd
  have hchecked := checkTree_sound 19 1572 certificate7 t (by omega) (by omega)
  exact passes_sound hchecked hhigh hg

/-- Complete classification over the range in Mientka--Weitzenkamp (1969). -/
theorem classification (n : ℕ) (hbound : n ≤ 2 ^ 44) : Good n ↔ n ∈ known := by
  constructor
  · intro hg
    by_cases h21 : n ≤ 21
    · exact small_classification n h21 hg
    have hd3 : 3 ∣ n := force3 n (by omega) hg
    have hd5 : 5 ∣ n := force5 n (by omega) hg
    have hd15 : 15 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 5) hd3 hd5
    by_cases h1035 : n ≤ 1035
    · exact case2 n (by omega) h1035 hd15 hg
    have hd11 : 11 ∣ n := force11 n (by omega) hg
    have hd165 : 165 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 15 11) hd15 hd11
    by_cases h4109 : n ≤ 4109
    · exact case3 n (by omega) h4109 hd165 hg
    have hd13 : 13 ∣ n := force13 n (by omega) hg
    have hd2145 : 2145 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 165 13) hd165 hd13
    by_cases h262163 : n ≤ 262163
    · exact case4 n (by omega) h262163 hd2145 hg
    have hd19 : 19 ∣ n := force19 n (by omega) hg
    have hd40755 : 40755 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2145 19) hd2145 hd19
    by_cases h268435485 : n ≤ 268435485
    · exact case5 n (by omega) h268435485 hd40755 hg
    have hd29 : 29 ∣ n := force29 n (by omega) hg
    have hd1181895 : 1181895 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 40755 29) hd40755 hd29
    by_cases h68719476773 : n ≤ 68719476773
    · exact case6 n (by omega) h68719476773 hd1181895 hg
    have hd37 : 37 ∣ n := force37 n (by omega) hg
    have hd43730115 : 43730115 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 1181895 37) hd1181895 hd37
    exact case7 n (by omega) (by simpa using hbound) hd43730115 hg
  · exact known_good n

/-- Original set equality: no zero/one vacuity and no restriction on the exponent omitted. -/
theorem mientka_weitzenkamp :
    {n : ℕ | n ≤ 2 ^ 44 ∧ Good n} = ({4, 7, 15, 21, 45, 75, 105} : Set ℕ) := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, hg⟩
    simpa [known] using (classification n hn).mp hg
  · intro hn
    have hmem : n ∈ known := by simpa [known] using hn
    have hb : n ≤ 2 ^ 44 := by
      have : ∀ n ∈ known, n ≤ 2 ^ 44 := by decide
      exact this n hmem
    exact ⟨hb, known_good n hmem⟩

end JSP000947
