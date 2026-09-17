"""Generate a standalone Lean proof from explicit clique-cover certificates.
The discovery optimizer is not used by Lean and is not a proof oracle.
This is a finite result, not a full solution or prize claim for JSP-000357.
"""
from pathlib import Path
import itertools
p = Path(__file__).resolve().parent
Q = {0, 1, 4, 9, 16, 17, 25}
V = {i for i in range(32) if 2*i % 32 not in Q}
maxima = [[1,5,9,10,13,14,17,21,25,29,30], [1,5,9,13,14,17,21,25,26,29,30]]
covers = {
3:[[1,3],[3,29],[4,12,13],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[15,17],[20,21,28]],
4:[[1,3],[4,12,29],[4,13,28],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[15,17],[20,21,28]],
6:[[1,31],[3,29],[4,12,13],[5,27],[6,10,26],[6,19,30],[7,25],[9,23],[11,14,22],[15,17],[20,21,28]],
7:[[1,3],[4,12,29],[5,27],[6,19,30],[7,9],[7,25],[10,26,31],[11,14,22],[13,23],[15,17],[20,21,28]],
11:[[1,3],[4,12,29],[5,27],[6,19,30],[7,9],[10,26,31],[11,14,22],[11,25],[13,23],[15,17],[20,21,28]],
12:[[1,3],[4,12,13],[4,12,29],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[15,17],[20,21,28]],
15:[[1,15],[3,14,22],[4,12,29],[5,27],[6,19,30],[7,9],[10,26,31],[11,25],[13,23],[15,17],[20,21,28]],
19:[[1,3],[4,12,29],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[13,19],[15,17],[20,21,28]],
20:[[1,3],[4,13,28],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[12,20,29],[15,17],[20,21,28]],
22:[[1,31],[3,14,22],[4,12,29],[5,27],[6,19,30],[7,9],[10,22,26],[11,25],[13,23],[15,17],[20,21,28]],
23:[[1,3],[4,12,29],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[13,23],[15,17],[20,21,28]],
27:[[1,3],[4,12,29],[5,27],[6,19,30],[7,9],[10,26,31],[11,25],[13,23],[14,22,27],[15,17],[20,21,28]],
28:[[1,3],[4,12,29],[4,13,28],[5,27],[6,19,30],[7,25],[9,23],[10,26,31],[11,14,22],[15,17],[20,21,28]],
31:[[1,31],[3,14,22],[4,12,29],[5,27],[6,19,30],[7,9],[10,26,31],[11,25],[13,23],[15,17],[20,21,28]]}
base = [[3,6,30],[4,5,12],[28,29],[7,25],[9,27],[10,23,26],[11,14,22],[20,21],[1,15],[17,31],[13,19]]
allc = sorted({tuple(sorted(c)) for cover in [base,*covers.values()] for c in cover})
cn = {c:'clique_'+'_'.join(map(str,c)) for c in allc}
for cover in [base,*covers.values()]:
    assert len(cover)==11
    assert V <= set().union(*map(set,cover))
    for c in cover:
        assert all((x+y)%32 in Q for x,y in itertools.combinations(c,2))
for r,cover in covers.items():
    assert sum(r in c for c in cover)>=2
for M in maxima:
    assert len(M)==11 and all((x+y)%32 not in Q for x in M for y in M)
forbidden = sorted(set(range(32))-V)
common = set(maxima[0]) & set(maxima[1])
optional = {10,26}
s = ['''/-
Copyright (c) 2026 Ketian Zhang. Released under the MIT license.

A standalone elementary proof of the sharp modulo-32 square-sum-free bound
and classification of both extremizers. Prepared with ChatGPT assistance.
The 11/32 construction/bound are established prior mathematics (Massias;
Lagarias--Odlyzko--Shearer). No mathematical or formalization priority claimed.
This finite theorem is NOT the full asymptotic theorem JSP-000357.
-/
import Std

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mod32

/-- All square residues modulo 32. -/
def Q (n : Nat) : Prop :=
  n % 32 = 0 ∨ n % 32 = 1 ∨ n % 32 = 4 ∨ n % 32 = 9 ∨
  n % 32 = 16 ∨ n % 32 = 17 ∨ n % 32 = 25

instance (n : Nat) : Decidable (Q n) := inferInstanceAs (Decidable
  (n % 32 = 0 ∨ n % 32 = 1 ∨ n % 32 = 4 ∨ n % 32 = 9 ∨
   n % 32 = 16 ∨ n % 32 = 17 ∨ n % 32 = 25))

/-- Zero-one indicator vectors, including all diagonal obstructions. -/
def Admissible (w : Fin 32 → Nat) : Prop :=
  (∀ i, w i ≤ 1) ∧ ∀ i j, Q (i.val + j.val) → w i + w j ≤ 1

/-- Cardinality is the sum of all 32 indicator entries. -/
def card (w : Fin 32 → Nat) : Nat :=
  ''' + ' + '.join('w '+str(i) for i in range(32)) + '\n']
for i in forbidden:
    s.append(f'''private theorem zero_{i} (w : Fin 32 → Nat) (h : Admissible w) : w {i} = 0 := by
  have hp := h.2 {i} {i} (by decide)
  omega
''')
for c in allc:
    s.append(f'private theorem {cn[c]} (w : Fin 32 → Nat) (h : Admissible w) :\n    '+' + '.join(f'w {i}' for i in c)+' ≤ 1 := by\n')
    for a,b in itertools.combinations(c,2):
        s.append(f'  have h{a}_{b} := h.2 {a} {b} (by decide)\n')
    s.append('  omega\n')
def usecover(cover):
    return ''.join(f'  have z{i} := zero_{i} w h\n' for i in forbidden)+''.join(f'  have c{k} := {cn[tuple(sorted(c))]} w h\n' for k,c in enumerate(cover))
s.append('''/-- Eleven cliques cover every non-forbidden residue. -/
theorem upper_bound (w : Fin 32 → Nat) (h : Admissible w) : card w ≤ 11 := by
'''+usecover(base)+'  unfold card\n  omega\n')
for i,cover in covers.items():
    s.append(f'''private theorem equality_zero_{i} (w : Fin 32 → Nat) (h : Admissible w)
    (hc : card w = 11) : w {i} = 0 := by
'''+usecover(cover)+'  unfold card at hc\n  omega\n')
for name,M in zip(['first','second'],maxima):
    s.append(f'def {name} (i : Fin 32) : Nat :=\n  if '+' ∨ '.join(f'i.val = {i}' for i in M)+' then 1 else 0\n')
s.append('''theorem first_admissible : Admissible first := by
  unfold Admissible
  decide

theorem second_admissible : Admissible second := by
  unfold Admissible
  decide

theorem first_card : card first = 11 := by decide

theorem second_card : card second = 11 := by decide

/-- All extremizers, with an actual equality proof rather than a search oracle. -/
theorem extremizers (w : Fin 32 → Nat) (h : Admissible w) (hc : card w = 11) :
    w = first ∨ w = second := by
''')
zeros = sorted(set(range(32))-common-optional)
for i in zeros:
    f=f'zero_{i}' if i in forbidden else f'equality_zero_{i}'
    s.append(f'  have z{i} := {f} w h'+(' hc' if i not in forbidden else '')+'\n')
for i in sorted(common|optional):
    s.append(f'  have b{i} := h.1 {i}\n')
s.append('  have bp := h.2 10 26 (by decide)\n  unfold card at hc\n')
for i in sorted(common):
    s.append(f'  have e{i} : w {i} = 1 := by omega\n')
s.append('  have es : w 10 + w 26 = 1 := by omega\n  have ht : w 10 = 1 ∨ w 10 = 0 := by omega\n  cases ht with\n')
for which,M in zip(['first','second'],maxima):
    tag='inl' if which=='first' else 'inr'
    s.append(f'  | {tag} h10 =>\n    apply Or.{tag}\n    funext i\n')
    s.append('    have hi : '+' ∨ '.join(f'i = {i}' for i in range(32))+' := by omega\n')
    s.append('    rcases hi with '+' | '.join('hi' for _ in range(32))+'\n')
    for i in range(32):
        value = int(i in M)
        s.append(f'    · subst i\n      change w {i} = {value}\n      omega\n')
s.append('''
/-- Boolean membership of any subset of Z/32Z. -/
def indicator (A : Fin 32 → Bool) (i : Fin 32) : Nat := if A i then 1 else 0

/-- Actual square congruences, with the diagonal included. -/
def SquareSumFree (A : Fin 32 → Bool) : Prop :=
  ∀ i j : Fin 32, A i = true → A j = true → ∀ z : Fin 32,
    (i.val + j.val) % 32 ≠ (z.val * z.val) % 32

private theorem square_residues : ∀ i j : Fin 32,
    Q (i.val + j.val) ↔ ∃ z : Fin 32,
      (i.val + j.val) % 32 = (z.val * z.val) % 32 := by decide

theorem admissible_indicator (A : Fin 32 → Bool) (h : SquareSumFree A) :
    Admissible (indicator A) := by
  constructor
  · intro i
    cases hi : A i <;> simp [indicator, hi]
  · intro i j hq
    cases hi : A i with
    | false =>
      cases hj : A j <;> simp [indicator, hi, hj]
    | true =>
      cases hj : A j with
      | false => simp [indicator, hi, hj]
      | true =>
        obtain ⟨z, hz⟩ := (square_residues i j).mp hq
        exact False.elim (h i j hi hj z hz)

/-- Upper bound for every subset, in the direct square-congruence formulation. -/
theorem square_free_card_bound (A : Fin 32 → Bool) (h : SquareSumFree A) :
    card (indicator A) ≤ 11 :=
  upper_bound (indicator A) (admissible_indicator A h)

/-- The two vectors exhaust all size-11 square-sum-free subsets. -/
theorem square_free_maxima (A : Fin 32 → Bool) (h : SquareSumFree A)
    (hc : card (indicator A) = 11) :
    indicator A = first ∨ indicator A = second :=
  extremizers (indicator A) (admissible_indicator A h) hc

#print axioms Mod32.upper_bound
#print axioms Mod32.extremizers
#print axioms Mod32.first_admissible
#print axioms Mod32.second_admissible
#print axioms Mod32.square_free_card_bound
#print axioms Mod32.square_free_maxima

end Mod32
''')
(p/'Mod32.lean').write_text('\n'.join(s))
(p/'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
(p/'lakefile.toml').write_text('name = "mod32"\nversion = "0.1.0"\ndefaultTargets = ["Mod32"]\n\n[[lean_lib]]\nname = "Mod32"\n')
print('Generated',len(('\n'.join(s)).splitlines()),'Lean lines.')
