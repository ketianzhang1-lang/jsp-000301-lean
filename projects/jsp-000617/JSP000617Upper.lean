import JSP000617Stages
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
The upper-asymptotic-density variant of Erdős 749 (JSP-000617).
This is distinct from the original lower-density problem.
The mathematical construction is attributed to Aron Bhalla and Terence Tao;
see README.md for sources and AI-assistance disclosure.
-/
namespace JSP000617

def sumset (A : Set ℕ) : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ A, a+b=n}

noncomputable def orderedRep (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter (fun ab => ab.1 ∈ A ∧ ab.2 ∈ A)).card

noncomputable def prefixSet (S : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n => n ∈ S)

/-- Standard upper asymptotic density, using the prefix [0,N). -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.atTop.limsup (fun N => ((prefixSet S N).card : ℝ) / (N : ℝ))

def infiniteSet (m : ℕ) (hK : 4 ≤ 2^m) : Set ℕ :=
  {a | ∃ j, a ∈ (stages m hK j).points}

lemma finite_capture (B : ℕ → Finset ℕ) (hB : Monotone B) (S : Finset ℕ)
    (hS : ∀ a ∈ S, ∃ j, a ∈ B j) : ∃ j, S ⊆ B j := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,Finset.empty_subset _⟩
  | @insert a S ha ih =>
    obtain ⟨i,hi⟩ := hS a (Finset.mem_insert_self _ _)
    obtain ⟨j,hj⟩ := ih (fun b hb => hS b (Finset.mem_insert_of_mem hb))
    refine ⟨max i j,Finset.insert_subset ?_ ?_⟩
    · exact hB (Nat.le_max_left _ _) hi
    · exact hj.trans (hB (Nat.le_max_right _ _))

theorem infinite_representations (m : ℕ) (hK : 4 ≤ 2^m) (n : ℕ) :
    orderedRep (infiniteSet m hK) n ≤ uniformBound m := by
  classical
  let S := (Finset.range (n+1)).filter (fun a => a ∈ infiniteSet m hK)
  obtain ⟨j,hj⟩ := finite_capture (fun j => (stages m hK j).points) (stages_mono m hK) S
    (fun a ha => (Finset.mem_filter.mp ha).2)
  let P := (Finset.antidiagonal n).filter
    (fun ab => ab.1 ∈ infiniteSet m hK ∧ ab.2 ∈ infiniteSet m hK)
  have hsub : P ⊆ natReps (stages m hK j).points (stages m hK j).points n := by
    intro ab hab
    obtain ⟨hab,hA⟩ := Finset.mem_filter.mp hab
    have he := Finset.mem_antidiagonal.mp hab
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hj ?_,hj ?_⟩,he⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hA.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hA.2⟩
  exact (Finset.card_le_card hsub).trans ((stages m hK j).bound n)

lemma stage_prefix_subset (m : ℕ) (hK : 4 ≤ 2^m) (j N : ℕ) :
    finitePrefixSums (stages m hK j).points N ⊆ prefixSet (sumset (infiniteSet m hK)) N := by
  classical
  intro s hs
  obtain ⟨hs,hN⟩ := Finset.mem_filter.mp hs
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hN,
    ⟨a,⟨j,(Finset.mem_product.mp hab).1⟩,b,⟨j,(Finset.mem_product.mp hab).2⟩,rfl⟩⟩

theorem infinite_dense_prefixes (m : ℕ) (hK : 4 ≤ 2^m) (j : ℕ) :
    ∃ N, j ≤ N ∧ 0 < N ∧
      (2^m-3)*N ≤ (2^m)*(prefixSet (sumset (infiniteSet m hK)) N).card := by
  obtain ⟨N,hj,hN,hgood⟩ := stages_dense m hK j
  refine ⟨N,hj,hN,hgood.trans ?_⟩
  exact Nat.mul_le_mul_left _ (Finset.card_le_card (stage_prefix_subset m hK (j+1) N))

lemma prefix_density_le_one (S : Set ℕ) (N : ℕ) :
    ((prefixSet S N).card : ℝ) / (N : ℝ) ≤ 1 := by
  classical
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast (show (prefixSet S N).card ≤ N by
    simpa [prefixSet] using Finset.card_filter_le (s:=Finset.range N) (p:=fun n => n ∈ S))

theorem fixed_upper_density (m : ℕ) (hK : 4 ≤ 2^m) :
    1 - 3 / ((2^m : ℕ) : ℝ) ≤ upperDensity (sumset (infiniteSet m hK)) := by
  apply Filter.le_limsup_of_frequently_le
  · apply Filter.frequently_atTop.mpr
    intro j
    obtain ⟨N,hj,hN,hgood⟩ := infinite_dense_prefixes m hK j
    refine ⟨N,hj,?_⟩
    have hk : 0 < ((2^m : ℕ) : ℝ) := by positivity
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hge : 3 ≤ 2^m := by omega
    have hreal := (Nat.cast_le (α:=ℝ)).mpr hgood
    push_cast [Nat.cast_sub hge] at hreal
    rw [le_div_iff₀ hNr]
    apply (mul_le_mul_iff_right₀ hk).mp
    have he : ((2^m : ℕ) : ℝ) * ((1 - 3 / ((2^m : ℕ) : ℝ)) * (N : ℝ)) =
        (((2^m : ℕ) : ℝ)-3)*(N : ℝ) := by field_simp
    rw [he]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hreal
  · exact Filter.isBoundedUnder_of ⟨1,fun N => prefix_density_le_one _ N⟩

/-- Complete upper-density variant: an actual infinite-scale subset of ℕ and
a single representation bound for every n. No lower-density assertion is made. -/
theorem upper_density_variant (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℕ, 1-ε ≤ upperDensity (sumset A) ∧
      ∃ C : ℕ, ∀ n : ℕ, orderedRep A n ≤ C := by
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (max (4:ℝ) (3/ε)) (show (1:ℝ)<2 by norm_num)
  have h4 : (4:ℝ) < 2^m := (le_max_left _ _).trans_lt hm
  have hK : 4 ≤ 2^m := by exact_mod_cast h4.le
  have hεpow : 3/ε < (2:ℝ)^m := (le_max_right _ _).trans_lt hm
  have hdiv : 3 / ((2^m : ℕ) : ℝ) ≤ ε := by
    have hmul : 3 < (2:ℝ)^m * ε := (div_lt_iff₀ hε).mp hεpow
    apply (div_le_iff₀ (show 0 < ((2^m : ℕ) : ℝ) by positivity)).mpr
    simpa only [Nat.cast_pow,Nat.cast_ofNat,mul_comm] using hmul.le
  refine ⟨infiniteSet m hK,?_,uniformBound m,infinite_representations m hK⟩
  exact (by linarith : 1-ε ≤ 1-3/((2^m : ℕ) : ℝ)).trans (fixed_upper_density m hK)

end JSP000617

#print axioms JSP000617.upper_density_variant
