import GraphCore

namespace CatlinComplete
open Finset CatlinCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cluster (v : Vertex) : Fin 5 := ⟨v.val / 3, by omega⟩
def middle (i j : Fin 5) : Fin 5 := ⟨(3 * (i.val + j.val)) % 5, by omega⟩
def separated (i j : Fin 5) : Prop :=
  i < j ∧ ((i.val + 2) % 5 = j.val ∨ (j.val + 2) % 5 = i.val)
instance (i j : Fin 5) : Decidable (separated i j) := by unfold separated; infer_instance

def clusterWeight (c : Fin 5 → ℕ) (i j : Fin 5) : ℕ :=
  if separated i j then if c (middle i j) = 3 then 2 else 1 else 0

def profileCost (c : Fin 5 → ℕ) : ℕ :=
  ∑ i, ∑ j, c i * c j * clusterWeight c i j

theorem profile_certificate : ∀ c : Fin 5 → Fin 4,
    (∑ i, (c i).val) = 8 → 8 ≤ profileCost (fun i => (c i).val) := by
  decide +kernel

theorem separated_endpoints : ∀ u v : Vertex,
    separated (cluster u) (cluster v) → u < v ∧ ¬adjacent u v := by decide

theorem common_in_middle : ∀ u v w : Vertex,
    separated (cluster u) (cluster v) → adjacent u w → adjacent w v →
      cluster w = middle (cluster u) (cluster v) := by decide

theorem cluster_size : ∀ i : Fin 5,
    ((univ : Finset Vertex).filter fun v => cluster v = i).card = 3 := by decide

def count (B : Finset Vertex) (i : Fin 5) : ℕ :=
  (B.filter fun v => cluster v = i).card

theorem count_le_three (B : Finset Vertex) (i : Fin 5) : count B i ≤ 3 := by
  rw [← cluster_size i]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ B))

theorem sum_counts (B : Finset Vertex) : ∑ i, count B i = B.card := by
  simpa [count] using Finset.sum_card_fiberwise_eq_card_filter B univ cluster

theorem full_cluster {B : Finset Vertex} {i : Fin 5} (h : count B i = 3)
    {w : Vertex} (hw : cluster w = i) : w ∈ B := by
  have heq : B.filter (fun v => cluster v = i) = univ.filter (fun v => cluster v = i) := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.filter_subset_filter _ (Finset.subset_univ B)
    · rw [cluster_size, ← h]
      exact le_rfl
  have hm : w ∈ B.filter (fun v => cluster v = i) := by
    rw [heq]
    simp [hw]
  exact (Finset.mem_filter.mp hm).1

theorem weight_le_demand {B : Finset Vertex} {u v : Vertex}
    (hu : u ∈ B) (hv : v ∈ B) :
    clusterWeight (count B) (cluster u) (cluster v) ≤ demand B u v := by
  unfold clusterWeight
  split_ifs with hsep hfull
  · obtain ⟨hlt, hnot⟩ := separated_endpoints u v hsep
    have hncommon : ¬∃ w : Vertex, w ∉ B ∧ adjacent u w ∧ adjacent w v := by
      rintro ⟨w, hw, huw, hwv⟩
      exact hw (full_cluster hfull (common_in_middle u v w hsep huw hwv))
    simp [demand, hu, hv, hlt, hnot, hncommon]
  · obtain ⟨hlt, hnot⟩ := separated_endpoints u v hsep
    by_cases hc : ∃ w : Vertex, w ∉ B ∧ adjacent u w ∧ adjacent w v
    · simp [demand, hu, hv, hlt, hnot, hc]
    · simp [demand, hu, hv, hlt, hnot, hc]
  · exact Nat.zero_le _

theorem regroup (B : Finset Vertex) (f : Fin 5 → ℕ) :
    ∑ u ∈ B, f (cluster u) = ∑ i, count B i * f i := by
  simpa [count] using (Finset.sum_fiberwise' B cluster f).symm

theorem regroup_twice (B : Finset Vertex) (f : Fin 5 → Fin 5 → ℕ) :
    ∑ u ∈ B, ∑ v ∈ B, f (cluster u) (cluster v) =
      ∑ i, ∑ j, count B i * count B j * f i j := by
  rw [regroup B (fun i => ∑ v ∈ B, f i (cluster v))]
  apply Finset.sum_congr rfl
  intro i _
  rw [regroup B (f i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (Nat.mul_assoc _ _ _).symm

theorem profileCost_le_budget (B : Finset Vertex) : profileCost (count B) ≤ budget B := by
  unfold profileCost budget
  rw [← regroup_twice B (clusterWeight (count B))]
  calc
    (∑ u ∈ B, ∑ v ∈ B, clusterWeight (count B) (cluster u) (cluster v))
        ≤ ∑ u ∈ B, ∑ v ∈ B, demand B u v := by
          apply Finset.sum_le_sum
          intro u hu
          apply Finset.sum_le_sum
          intro v hv
          exact weight_le_demand hu hv
    _ ≤ ∑ u ∈ B, ∑ v, demand B u v := by
      apply Finset.sum_le_sum
      intro u _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (by intros; omega)
    _ ≤ ∑ u, ∑ v, demand B u v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (by intros; omega)

theorem budget_ge_eight (B : Finset Vertex) (hB : B.card = 8) : 8 ≤ budget B := by
  let c : Fin 5 → Fin 4 := fun i => ⟨count B i, by have := count_le_three B i; omega⟩
  have hc : ∑ i, (c i).val = 8 := by simpa [c, sum_counts] using hB
  exact (profile_certificate c hc).trans (profileCost_le_budget B)

end CatlinComplete
