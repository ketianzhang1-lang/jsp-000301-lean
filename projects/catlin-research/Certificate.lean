import Std

/-!
Finite certificates for the known Catlin graph C5[K3].

Scope: these declarations verify the finite arithmetic obstruction, a proper
8-colouring, and the absence of an independent triple. The graph-theoretic
bridge for a simpler sufficient obstruction is now formalized in
GraphCore.lean, Profile.lean and Subdivision.lean. This file is NOT a complete Lean proof
of Erdos 717 / JSP-000585, whose conclusion is asymptotic.

The underlying counterexample is credited to Catlin. No mathematical novelty,
priority, official verification, award, or payment is asserted.
-/

namespace CatlinCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Vertex := Fin 15

def adjacent (u v : Vertex) : Prop :=
  u.val ≠ v.val ∧
    (u.val / 3 = v.val / 3 ∨
      (u.val / 3 + 1) % 5 = v.val / 3 ∨
      (v.val / 3 + 1) % 5 = u.val / 3)

instance (u v : Vertex) : Decidable (adjacent u v) := by
  unfold adjacent
  infer_instance

def colour (v : Vertex) : Nat :=
  match v.val with
  | 0 | 6 => 0
  | 1 | 7 => 1
  | 2 | 9 => 2
  | 3 | 10 => 3
  | 4 | 11 => 4
  | 5 | 12 => 5
  | 8 | 13 => 6
  | _ => 7

theorem eight_colours : ∀ v : Vertex, colour v < 8 := by decide

theorem proper_eight_colouring :
    ∀ u v : Vertex, adjacent u v → colour u ≠ colour v := by decide

theorem no_independent_triple :
    ∀ x y z : Vertex, x ≠ y → x ≠ z → y ≠ z →
      adjacent x y ∨ adjacent x z ∨ adjacent y z := by decide

/-- Number of nonadjacent pairs among the eight branch vertices. -/
def missingPairs (a b c d e : Nat) : Nat :=
  a * c + b * d + c * e + d * a + e * b

/-- Necessary lower bound on internal vertices in a clique subdivision. -/
def requiredInternal (a b c d e : Nat) : Nat :=
  missingPairs a b c d e +
    (a * c - (3 - b)) + (b * d - (3 - c)) +
    (c * e - (3 - d)) + (d * a - (3 - e)) +
    (e * b - (3 - a))

/-- Exhaustive check of all 4^5 tuples, not a sampled search. -/
theorem finite_budget_certificate :
    ∀ a b c d e : Fin 4,
      a.val + b.val + c.val + d.val + e.val = 8 →
      12 ≤ requiredInternal a.val b.val c.val d.val e.val := by decide

theorem budget_bound (a b c d e : Nat)
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4)
    (hs : a + b + c + d + e = 8) :
    12 ≤ requiredInternal a b c d e :=
  finite_budget_certificate ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ ⟨e, he⟩ hs

/-- This is a resource-inequality theorem, not a theorem about graph paths. -/
theorem no_feasible_resource_tuple (a b c d e : Nat)
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4)
    (hs : a + b + c + d + e = 8)
    (havailable : requiredInternal a b c d e ≤ 7) : False :=
  (by decide : ¬ (12 ≤ 7))
    (Nat.le_trans (budget_bound a b c d e ha hb hc hd he hs) havailable)

#print axioms eight_colours
#print axioms proper_eight_colouring
#print axioms no_independent_triple
#print axioms finite_budget_certificate
#print axioms budget_bound
#print axioms no_feasible_resource_tuple

end CatlinCertificates
