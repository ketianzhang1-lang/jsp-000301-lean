import Mathlib.Tactic

/-!
# JSP-000392: Schur lower bounds

Independent formalization of known constructions, assisted by OpenAI ChatGPT.
The explicit five-color seed is due to Geoffrey Exoo (1994), EJC 1, R8.
The tripling construction is classical. This does not settle the asymptotic
Schur-number problem. Equal summands are allowed throughout.
-/
namespace JSP000392

/-- A coloring of the positive interval `[1,N]` using colors `< k`, with no
monochromatic solution of `x + y = z`. Values outside the interval are irrelevant. -/
def Valid (k N : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ x, 1 ≤ x → x ≤ N → c x < k) ∧
  ∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ N → c x = c y → c x ≠ c (x + y)

/-- There exists a sum-free coloring using at most `k` colors. -/
def Colorable (k N : ℕ) : Prop := ∃ c : ℕ → ℕ, Valid k N c

/-- Classical reflection construction: keep the old colors on the lower
interval, reflect them on the upper interval, and use one new middle color. -/
def liftColor (k N : ℕ) (c : ℕ → ℕ) (x : ℕ) : ℕ :=
  if x ≤ N then c x else if x ≤ 2 * N + 1 then k else c (3 * N + 2 - x)

theorem lift_valid {k N : ℕ} {c : ℕ → ℕ} (h : Valid k N c) :
    Valid (k + 1) (3 * N + 1) (liftColor k N c) := by
  rcases h with ⟨hb, hs⟩
  constructor
  · intro x hx hX
    unfold liftColor
    split_ifs with h1 h2
    · exact lt_trans (hb x hx h1) (Nat.lt_succ_self k)
    · omega
    · have hh := hb (3 * N + 2 - x) (by omega) (by omega)
      omega
  · intro x y hx hy hxy heq hsum
    unfold liftColor at heq hsum
    split_ifs at heq hsum <;> try omega
    all_goals first
      | exact hs x y hx hy (by omega) heq hsum
      | have hh := hb x hx (by omega); omega
      | have hh := hb y hy (by omega); omega
      | have hh := hb (3 * N + 2 - (x + y)) (by omega) (by omega); omega
      | skip
    · have hid : x + (3 * N + 2 - (x + y)) = 3 * N + 2 - y := by omega
      have hbad := hs x (3 * N + 2 - (x + y)) hx (by omega) (by omega) hsum
      rw [hid] at hbad
      exact hbad heq
    · have hid : y + (3 * N + 2 - (x + y)) = 3 * N + 2 - x := by omega
      have hbad := hs y (3 * N + 2 - (x + y)) hy (by omega) (by omega)
        (heq.symm.trans hsum)
      rw [hid] at hbad
      exact hbad heq.symm

theorem tripling {k N : ℕ} (h : Colorable k N) : Colorable (k + 1) (3 * N + 1) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨liftColor k N c, lift_valid hc⟩

/-- Exoo's published symmetric coloring. The lower half is transcribed from
page 2 of EJC 1 (1994), R8, and the upper half uses symmetry `x ↦ 161-x`. -/
def seedHalf (x : ℕ) : ℕ :=
  if x ∈ ([4,5,15,16,22,28,29,39,40,41,42,48,49,59] : List ℕ) then 0
  else if x ∈ ([2,3,8,14,19,20,24,25,36,46,47,51,62,73] : List ℕ) then 1
  else if x ∈ ([7,9,11,12,13,17,27,31,32,33,35,37,53,56,57,61,79] : List ℕ) then 2
  else if x ∈ ([1,6,10,18,21,23,26,30,34,38,43,45,50,54,65,74] : List ℕ) then 3
  else 4

def seed (x : ℕ) : ℕ := seedHalf (if x ≤ 80 then x else 161 - x)

-- Finite arithmetic certificate, evaluated by Lean's kernel, not native_decide.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_certificate :
    (∀ x : Fin 161, seed x.val < 5) ∧
    (∀ x y : Fin 161, 1 ≤ x.val → 1 ≤ y.val → x.val + y.val ≤ 160 →
      seed x.val = seed y.val → seed x.val ≠ seed (x.val + y.val)) := by
  decide +kernel

theorem exoo_160 : Colorable 5 160 := by
  refine ⟨seed, ?_, ?_⟩
  · intro x hx hX
    exact seed_certificate.1 ⟨x, by omega⟩
  · intro x y hx hy hxy
    exact seed_certificate.2 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy hxy

/-- Repeated tripling, starting from an arbitrary valid seed. -/
def capacity (N : ℕ) : ℕ → ℕ
  | 0 => N
  | r + 1 => 3 * capacity N r + 1

theorem capacity_identity (N r : ℕ) :
    2 * capacity N r + 1 = (2 * N + 1) * 3 ^ r := by
  induction r with
  | zero => simp [capacity]
  | succ r ih =>
    simp only [capacity, pow_succ]
    rw [← Nat.mul_assoc, ← ih]
    omega

theorem iterate_tripling {k N : ℕ} (h : Colorable k N) (r : ℕ) :
    Colorable (k + r) (capacity N r) := by
  induction r with
  | zero => simpa [capacity] using h
  | succ r ih => simpa [capacity, Nat.add_assoc] using tripling ih

theorem general_seed_family {k N : ℕ} (h : Colorable k N) (r : ℕ) :
    Colorable (k + r) (((2 * N + 1) * 3 ^ r - 1) / 2) := by
  have hid := capacity_identity N r
  have he : ((2 * N + 1) * 3 ^ r - 1) / 2 = capacity N r := by omega
  rw [he]
  exact iterate_tripling h r

/-- For every r≥0, there is a (5+r)-coloring of the first
(321·3^r−1)/2 positive integers without a monochromatic Schur triple. -/
theorem exoo_family (r : ℕ) : Colorable (5 + r) ((321 * 3 ^ r - 1) / 2) := by
  simpa using general_seed_family exoo_160 r

/-- In the forcing-threshold convention, no N at or below this bound forces
monochromatic x+y=z. This explicitly distinguishes S(k) from S(k)+1. -/
def Forces (k N : ℕ) : Prop :=
  ∀ c : ℕ → ℕ, (∀ x, 1 ≤ x → x ≤ N → c x < k) →
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ N ∧ c x = c y ∧ c x = c (x + y)

theorem colorable_not_forces {k N : ℕ} (h : Colorable k N) : ¬ Forces k N := by
  obtain ⟨c, hb, hs⟩ := h
  intro hf
  obtain ⟨x, y, hx, hy, hxy, hc, hc'⟩ := hf c hb
  exact hs x y hx hy hxy hc hc'

theorem exoo_forcing_lower (r : ℕ) : ¬ Forces (5+r) ((321 * 3^r - 1)/2) :=
  colorable_not_forces (exoo_family r)

/-- Difference coloring of the edges on vertices `0,...,N`.
The triple condition is stated for ordered vertices; every triangle has one
unique increasing ordering. Thus it covers all triangles. -/
def TriangleColorable (k N : ℕ) : Prop :=
  ∃ e : ℕ → ℕ → ℕ,
    (∀ x y, e x y = e y x) ∧
    (∀ x y, x < y → y ≤ N → e x y < k) ∧
    ∀ x y z, x < y → y < z → z ≤ N → e x y = e y z → e x y ≠ e x z

theorem difference_coloring {k N : ℕ} (h : Colorable k N) :
    TriangleColorable k N := by
  obtain ⟨c, hb, hs⟩ := h
  refine ⟨fun x y => c (x-y+(y-x)), ?_, ?_, ?_⟩
  · intro x y
    simp only [Nat.add_comm]
  · intro x y hxy hy
    have hd : x-y+(y-x) = y-x := by omega
    change c (x-y+(y-x)) < k
    rw [hd]
    exact hb (y-x) (by omega) (by omega)
  · intro x y z hxy hyz hz heq
    have h1 : x-y+(y-x) = y-x := by omega
    have h2 : y-z+(z-y) = z-y := by omega
    have h3 : x-z+(z-x) = z-x := by omega
    simp only [h1, h2, h3] at heq ⊢
    have hid : (y-x)+(z-y)=z-x := by omega
    have hbad := hs (y-x) (z-y) (by omega) (by omega) (by omega) heq
    simpa only [hid] using hbad

theorem exoo_ramsey_family (r : ℕ) :
    TriangleColorable (5+r) ((321 * 3^r - 1)/2) :=
  difference_coloring (exoo_family r)

end JSP000392
