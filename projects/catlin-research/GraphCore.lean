import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic
import Certificate

namespace CatlinComplete
open Finset CatlinCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def graph : SimpleGraph Vertex where
  Adj := adjacent
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent _ _))

def demand (B : Finset Vertex) (u v : Vertex) : ℕ :=
  if u ∈ B ∧ v ∈ B ∧ u < v ∧ ¬adjacent u v then
    if ∃ w : Vertex, w ∉ B ∧ adjacent u w ∧ adjacent w v then 1 else 2
  else 0

def budget (B : Finset Vertex) : ℕ := ∑ u, ∑ v, demand B u v

def inside {u v : Vertex} (p : graph.Walk u v) : Finset Vertex :=
  (p.support.toFinset.erase u).erase v

@[simp] theorem mem_inside {u v x : Vertex} {p : graph.Walk u v} :
    x ∈ inside p ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := by
  simp [inside, and_assoc, and_left_comm, and_comm]

theorem card_inside {u v : Vertex} (p : graph.Walk u v) (hp : p.IsPath)
    (huv : u ≠ v) : (inside p).card = p.length - 1 := by
  have hu : u ∈ p.support.toFinset := by simp
  have hv : v ∈ p.support.toFinset := by simp
  have hve : v ∈ p.support.toFinset.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  rw [inside, Finset.card_erase_of_mem hve, Finset.card_erase_of_mem hu,
    List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  omega

theorem length_ge_two {u v : Vertex} (p : graph.Walk u v)
    (huv : u ≠ v) (hn : ¬graph.Adj u v) : 2 ≤ p.length := by
  cases p with
  | nil => exact False.elim (huv rfl)
  | cons h q =>
    cases q with
    | nil => exact False.elim (hn h)
    | cons h' q => simp

theorem length_ge_three {B : Finset Vertex} {u v : Vertex}
    (p : graph.Walk u v) (hp : p.IsPath) (huv : u ≠ v)
    (hn : ¬graph.Adj u v) (havoid : Disjoint (inside p) B)
    (hcommon : ¬∃ w : Vertex, w ∉ B ∧ graph.Adj u w ∧ graph.Adj w v) :
    3 ≤ p.length := by
  cases p with
  | nil => exact False.elim (huv rfl)
  | @cons _ w _ h q =>
    cases q with
    | nil => exact False.elim (hn h)
    | @cons _ z _ h' q =>
      cases q with
      | nil =>
        exfalso
        apply hcommon
        refine ⟨w, ?_, h, h'⟩
        intro hw
        have hm : w ∈ inside (SimpleGraph.Walk.cons h (SimpleGraph.Walk.cons h' .nil)) := by
          simp only [mem_inside]
          exact ⟨by simp, graph.ne_of_adj h |>.symm, graph.ne_of_adj h'⟩
        exact (Finset.disjoint_left.mp havoid) hm hw
      | cons h'' q => simp

theorem demand_le_inside {B : Finset Vertex} {u v : Vertex}
    (p : graph.Walk u v) (hp : p.IsPath) (huv : u < v)
    (havoid : Disjoint (inside p) B) : demand B u v ≤ (inside p).card := by
  unfold demand
  split_ifs with h hc
  · have hlen := length_ge_two p (ne_of_lt huv) h.2.2.2
    rw [card_inside p hp (ne_of_lt huv)]
    omega
  · have hlen := length_ge_three p hp (ne_of_lt huv) h.2.2.2 havoid hc
    rw [card_inside p hp (ne_of_lt huv)]
    omega
  · exact Nat.zero_le _

end CatlinComplete
