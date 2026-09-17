import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

/-!
# JSP-000728: the Cameron–Erdős lower bound

The classical construction is described in Balogh, Liu, Sharifzadeh and Treglown,
arXiv:1409.5661, Section 1. This independently written formalization covers the
lower bound for every interval, not the asymptotic upper bound.
Prepared with OpenAI ChatGPT assistance.
-/

namespace JSP000728

def SumFree (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A

def MaximalSumFree (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ SumFree A ∧
    ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N → SumFree B → A ⊆ B → B = A

noncomputable def maximalSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter (MaximalSumFree N)

theorem mem_maximalSets (N : ℕ) (A : Finset ℕ) :
    A ∈ maximalSets N ↔ MaximalSumFree N A := by
  classical
  simp only [maximalSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

theorem exists_maximal_extension {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hs : SumFree A) :
    ∃ B, A ⊆ B ∧ MaximalSumFree N B := by
  classical
  let F := (Finset.Icc 1 N).powerset.filter SumFree
  have ha : A ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hs⟩
  obtain ⟨B, hAB, hB, hmax⟩ := F.exists_le_maximal ha
  have hb := Finset.mem_filter.mp hB
  refine ⟨B, hAB, Finset.mem_powerset.mp hb.1, hb.2, ?_⟩
  intro C hC hsC hBC
  exact Finset.Subset.antisymm
    (hmax (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC, hsC⟩) hBC) hBC

def pick (m : ℕ) (b : Fin m → Bool) (i : Fin m) : ℕ :=
  if b i then 2 * i.val + 1 else 4 * m - (2 * i.val + 1)

def seed (m : ℕ) (b : Fin m → Bool) : Finset ℕ :=
  insert (4 * m) (Finset.univ.image (pick m b))

theorem pick_bounds {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    0 < pick m b i ∧ pick m b i < 4 * m ∧ pick m b i % 2 = 1 := by
  have hi := i.isLt
  unfold pick
  split <;> omega

theorem pick_sum_ne {m : ℕ} (b : Fin m → Bool) (i j : Fin m) :
    pick m b i + pick m b j ≠ 4 * m := by
  have hi := i.isLt
  have hj := j.isLt
  unfold pick
  split_ifs with hbi hbj hbj
  · omega
  · intro h
    have hij : i = j := Fin.ext (by omega)
    subst j
    simp_all
  · intro h
    have hij : i = j := Fin.ext (by omega)
    subst j
    simp_all
  · omega

theorem seed_subset {N m : ℕ} (hm : 0 < m) (hN : 4 * m ≤ N)
    (b : Fin m → Bool) : seed m b ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [seed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hx
  rcases hx with rfl | ⟨i, rfl⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, hN⟩
  · have h := pick_bounds b i
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem seed_sumFree {m : ℕ} (hm : 0 < m) (b : Fin m → Bool) :
    SumFree (seed m b) := by
  intro x hx y hy hz
  simp only [seed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hx hy hz
  rcases hx with rfl | ⟨i, rfl⟩ <;>
    rcases hy with rfl | ⟨j, rfl⟩ <;>
    rcases hz with h | ⟨k, h⟩
  · omega
  · have hk := pick_bounds b k; omega
  · have hj := pick_bounds b j; omega
  · have hj := pick_bounds b j; have hk := pick_bounds b k; omega
  · have hi := pick_bounds b i; omega
  · have hi := pick_bounds b i; have hk := pick_bounds b k; omega
  · exact pick_sum_ne b i j h
  · have hi := pick_bounds b i
    have hj := pick_bounds b j
    have hk := pick_bounds b k
    omega

theorem different_choices_incompatible {m : ℕ} {b c : Fin m → Bool}
    {A : Finset ℕ} (hs : SumFree A) (hb : seed m b ⊆ A)
    (hc : seed m c ⊆ A) : b = c := by
  funext i
  by_contra h
  have hbi : pick m b i ∈ A := hb (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hci : pick m c i ∈ A := hc (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hsnt : 4 * m ∈ A := hb (Finset.mem_insert_self _ _)
  have heq : pick m b i + pick m c i = 4 * m := by
    have hi := i.isLt
    unfold pick
    cases hbi' : b i <;> cases hci' : c i <;> simp_all <;> omega
  exact hs _ hbi _ hci (heq ▸ hsnt)

theorem lower_bound_multiple {N m : ℕ} (hm : 0 < m) (hN : 4 * m ≤ N) :
    2 ^ m ≤ (maximalSets N).card := by
  classical
  have hext (b : Fin m → Bool) :=
    exists_maximal_extension (seed_subset hm hN b) (seed_sumFree hm b)
  choose F hF hmax using hext
  have hinj : Function.Injective F := by
    intro b c h
    exact different_choices_incompatible (hmax b).2.1 (hF b) (h ▸ hF c)
  have hcard := Finset.card_le_card (show Finset.univ.image F ⊆ maximalSets N from by
    intro A hA
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hA
    exact (mem_maximalSets _ _).mpr (hmax b))
  simpa [Finset.card_image_of_injective _ hinj] using hcard

/-- Every interval `{1,...,N}` has at least `2^(floor(N/4))` inclusion-maximal
sum-free subsets. Repeated summands are forbidden as in the original problem. -/
theorem cameron_erdos_lower_bound (N : ℕ) :
    2 ^ (N / 4) ≤ (maximalSets N).card := by
  classical
  by_cases h : N / 4 = 0
  · have hs : SumFree ∅ := by simp [SumFree]
    obtain ⟨A, _, hA⟩ := exists_maximal_extension (Finset.empty_subset _) hs
    have hc : 0 < (maximalSets N).card := Finset.card_pos.mpr
      ⟨A, (mem_maximalSets _ _).mpr hA⟩
    simpa [h] using hc
  · exact lower_bound_multiple (by omega) (by omega)

#print axioms cameron_erdos_lower_bound

end JSP000728
