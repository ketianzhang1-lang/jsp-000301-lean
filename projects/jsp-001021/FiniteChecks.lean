import Mathlib.Tactic

/-!
Kernel-checked local exclusion certificates for our fifteen-vertex reproduction.
The witness search is untrusted: Lean checks all 196 pairs by ordinary `decide`.
This is one finite part of that reproduction. The complete main Lean proof uses
the separately attributed fourteen-vertex theorem and does not assume this
finite check alone proves the full combinatorial reduction.
-/

namespace JSP001021.LocalChecks
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

def paley (i j : ℕ) : Bool :=
  let d := (j + 7 - i) % 7
  d == 1 || d == 2 || d == 4

/-- Indices 0,...,6 denote O_i; indices 7,...,13 denote I_i. -/
def incoming (c : Fin 14) (i : ℕ) : Bool :=
  if c.val < 7 then paley (c.val % 7) i else paley i (c.val % 7)

def intersectionSize (c d : Fin 14) : ℕ :=
  ((List.range 7).filter fun i => incoming c i && incoming d i).length

/-- B=0,...,6; v=7; a=8; b=9, with B->v->a,b and a->b. -/
def localArc (c d : Fin 14) (i j : Fin 10) : Bool :=
  if i == j then false
  else if i.val < 7 then
    if j.val < 7 then paley i.val j.val
    else if j.val == 7 then true
    else if j.val == 8 then incoming c i.val else incoming d i.val
  else if i.val == 7 then decide (8 ≤ j.val)
  else if i.val == 8 then
    if j.val < 7 then !(incoming c j.val) else j.val == 9
  else if j.val < 7 then !(incoming d j.val) else false

def retained (c d : Fin 14) : Bool :=
  (decide (c.val < 7) && decide (7 ≤ d.val) && paley (c.val % 7) (d.val % 7)) ||
  (decide (7 ≤ c.val) && decide (7 ≤ d.val) && paley (d.val % 7) (c.val % 7))

def witnessTable : Array (List (Fin 10)) := #[
  [],
  [8, 3, 5, 9, 0],
  [8, 3, 9, 5, 0],
  [4, 8, 5, 9, 6],
  [8, 5, 6, 9, 0],
  [2, 8, 6, 9, 3],
  [1, 8, 3, 9, 5],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [2, 8, 4, 9, 6],
  [],
  [8, 4, 6, 9, 1],
  [8, 0, 4, 9, 1],
  [5, 8, 6, 9, 0],
  [8, 0, 9, 4, 1],
  [3, 8, 0, 9, 4],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [4, 8, 1, 9, 5],
  [3, 8, 5, 9, 0],
  [],
  [8, 0, 9, 1, 2],
  [8, 1, 5, 9, 2],
  [6, 8, 0, 9, 1],
  [8, 0, 1, 9, 2],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [8, 1, 2, 9, 3],
  [5, 8, 2, 9, 6],
  [4, 8, 6, 9, 1],
  [],
  [8, 1, 9, 2, 3],
  [8, 2, 6, 9, 3],
  [0, 8, 1, 9, 2],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [1, 8, 2, 9, 3],
  [8, 2, 3, 9, 4],
  [6, 8, 3, 9, 0],
  [5, 8, 0, 9, 2],
  [],
  [8, 0, 2, 9, 4],
  [8, 0, 9, 2, 4],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [8, 1, 9, 3, 5],
  [2, 8, 3, 9, 4],
  [8, 3, 4, 9, 5],
  [0, 8, 4, 9, 1],
  [6, 8, 1, 9, 3],
  [],
  [8, 1, 3, 9, 5],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [8, 2, 4, 9, 6],
  [8, 2, 9, 4, 6],
  [3, 8, 4, 9, 5],
  [8, 4, 5, 9, 6],
  [1, 8, 5, 9, 2],
  [0, 8, 2, 9, 4],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [5, 8, 0, 9, 2],
  [],
  [6, 8, 0, 9, 1],
  [3, 8, 0, 9, 4],
  [],
  [6, 8, 0, 9, 1],
  [5, 8, 0, 9, 2],
  [],
  [3, 8, 0, 9, 4],
  [],
  [],
  [4, 8, 1, 9, 5],
  [],
  [],
  [],
  [6, 8, 1, 9, 3],
  [],
  [0, 8, 1, 9, 2],
  [],
  [],
  [0, 8, 1, 9, 2],
  [6, 8, 1, 9, 3],
  [],
  [4, 8, 1, 9, 5],
  [],
  [1, 8, 2, 9, 3],
  [5, 8, 2, 9, 6],
  [],
  [],
  [],
  [0, 8, 2, 9, 4],
  [],
  [],
  [],
  [],
  [1, 8, 2, 9, 3],
  [0, 8, 2, 9, 4],
  [],
  [5, 8, 2, 9, 6],
  [],
  [2, 8, 3, 9, 4],
  [6, 8, 3, 9, 0],
  [],
  [],
  [],
  [1, 8, 3, 9, 5],
  [6, 8, 3, 9, 0],
  [],
  [],
  [],
  [2, 8, 3, 9, 4],
  [1, 8, 3, 9, 5],
  [],
  [2, 8, 4, 9, 6],
  [],
  [3, 8, 4, 9, 5],
  [0, 8, 4, 9, 1],
  [],
  [],
  [],
  [],
  [0, 8, 4, 9, 1],
  [],
  [],
  [],
  [3, 8, 4, 9, 5],
  [2, 8, 4, 9, 6],
  [],
  [3, 8, 5, 9, 0],
  [],
  [4, 8, 5, 9, 6],
  [1, 8, 5, 9, 2],
  [],
  [],
  [3, 8, 5, 9, 0],
  [],
  [1, 8, 5, 9, 2],
  [],
  [],
  [],
  [4, 8, 5, 9, 6],
  [],
  [],
  [4, 8, 6, 9, 1],
  [],
  [5, 8, 6, 9, 0],
  [2, 8, 6, 9, 3],
  [],
  [5, 8, 6, 9, 0],
  [4, 8, 6, 9, 1],
  [],
  [2, 8, 6, 9, 3],
  [],
  [],
  []]

def witness (c d : Fin 14) : List (Fin 10) :=
  witnessTable[c.val * 14 + d.val]?.getD []

/-- Each relevant pair either has an explicit transitive five-set or belongs
to one of the two retained pattern families. All 196 pairs are checked. -/
theorem local_exclusions : ∀ c d : Fin 14, intersectionSize c d = 1 →
    ((witness c d).length = 5 ∧
      (witness c d).Pairwise (fun i j => i ≠ j ∧ localArc c d i j = true)) ∨
    retained c d = true := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide

theorem retained_count :
    ((List.finRange 14).flatMap fun c =>
      (List.finRange 14).filter fun d => retained c d).length = 42 := by
  decide

def finalArc (i j : Fin 15) : Bool :=
  if i == j then false
  else if i.val < 7 then
    if j.val < 7 then paley i.val j.val
    else if j.val == 7 then true else paley i.val (j.val - 8)
  else if i.val == 7 then decide (8 ≤ j.val)
  else if j.val < 7 then (i.val - 8 == j.val) || paley (i.val - 8) j.val
  else if j.val == 7 then false else paley (j.val - 8) (i.val - 8)

/-- A0, B1, A5, B2, A3 is an ordered transitive five-set in the forced model. -/
theorem final_transitive_five :
    ([8, 1, 13, 2, 11] : List (Fin 15)).Pairwise
      (fun i j => i ≠ j ∧ finalArc i j = true) := by
  decide

end JSP001021.LocalChecks
