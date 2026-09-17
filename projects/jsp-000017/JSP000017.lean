import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

/-!
Known special cases of the lonely runner conjecture (JSP-000017).
This file does not prove the conjecture for unrestricted numbers of runners.
The formalization was prepared with OpenAI ChatGPT assistance.
-/

namespace JSP000017

/-- Membership in a closed safe interval modulo one. -/
def Safe (δ x : ℝ) : Prop :=
  ∃ z : ℤ, (z : ℝ) + δ ≤ x ∧ x ≤ (z : ℝ) + 1 - δ

theorem norm_ge_of_safe {δ x : ℝ} (h : Safe δ x) :
    δ ≤ ‖(x : UnitAddCircle)‖ := by
  obtain ⟨z, hlo, hhi⟩ := h
  rw [UnitAddCircle.norm_eq]
  rcases le_or_gt (round x) z with h | h
  · have hc : (round x : ℝ) ≤ z := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self _)
  · have hc : (z : ℝ) + 1 ≤ round x := by exact_mod_cast h
    exact le_trans (by linarith) (neg_le_abs _)

/-- Every interval of length `2δ` meets a safe interval. -/
theorem exists_safe_between {δ x y : ℝ} (hδ : 0 ≤ δ) (hhalf : δ ≤ 1/2)
    (hwidth : x + 2*δ ≤ y) :
    ∃ u, x ≤ u ∧ u ≤ y ∧ Safe δ u := by
  let z : ℤ := ⌊x - δ⌋
  have hzlo : (z : ℝ) ≤ x - δ := Int.floor_le _
  have hzhi : x - δ < (z : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases h : x ≤ (z : ℝ) + 1 - δ
  · exact ⟨x, le_rfl, by linarith, z, by linarith, h⟩
  · refine ⟨(z : ℝ) + 1 + δ, by linarith, by linarith, z+1, ?_, ?_⟩ <;>
      push_cast <;> linarith

/-- Two positive relative speeds, with no arithmetic restriction. -/
theorem two_positive_speeds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ t : ℝ, 0 < t ∧ Safe (1/3) (t*a) ∧ Safe (1/3) (t*b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  by_cases h : b ≤ 2*a
  · refine ⟨1/(3*a), by positivity, ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩ <;>
      simp only [Int.cast_zero, zero_add] <;> field_simp <;> nlinarith
  · have hr : b/(3*a) + 2*(1/3) ≤ 2*b/(3*a) := by
      apply (le_div_iff₀ (by positivity : 0 < 3*a)).mpr
      field_simp
      nlinarith
    obtain ⟨u, hul, huh, hu⟩ := exists_safe_between (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (1/3:ℝ) ≤ 1/2) hr
    refine ⟨u/b, div_pos (lt_of_lt_of_le (by positivity) hul) hb,
      ⟨0, ?_, ?_⟩, ?_⟩
    · simp only [Int.cast_zero, zero_add]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hb).mpr
      field_simp at hul ⊢
      nlinarith
    · simp only [Int.cast_zero, zero_add]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hb).mpr
      field_simp at huh ⊢
      nlinarith
    · simpa [ne_of_gt hb] using hu

theorem norm_abs_speed (t v : ℝ) :
    ‖(t*|v| : UnitAddCircle)‖ = ‖(t*v : UnitAddCircle)‖ := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h]
  · simp [abs_of_neg h]

/-- For any two nonzero real relative velocities, a positive lonely time exists. -/
theorem two_real_speeds {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (1/3:ℝ) ≤ ‖(t*a : UnitAddCircle)‖ ∧
      (1/3:ℝ) ≤ ‖(t*b : UnitAddCircle)‖ := by
  rcases le_total |a| |b| with h | h
  · obtain ⟨t, ht, hta, htb⟩ := two_positive_speeds (abs_pos.mpr ha) h
    exact ⟨t, ht, (norm_abs_speed t a) ▸ norm_ge_of_safe hta,
      (norm_abs_speed t b) ▸ norm_ge_of_safe htb⟩
  · obtain ⟨t, ht, htb, hta⟩ := two_positive_speeds (abs_pos.mpr hb) h
    exact ⟨t, ht, (norm_abs_speed t a) ▸ norm_ge_of_safe hta,
      (norm_abs_speed t b) ▸ norm_ge_of_safe htb⟩

theorem relative_distance (t a b : ℝ) :
    dist (t*a : UnitAddCircle) (t*b) = ‖(t*(a-b) : UnitAddCircle)‖ := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  congr 2
  ring

theorem three_speeds {v₀ v₁ v₂ : ℝ} (h₁ : v₀ ≠ v₁) (h₂ : v₀ ≠ v₂) :
    ∃ t : ℝ, 0 < t ∧ (1/3:ℝ) ≤ dist (t*v₀ : UnitAddCircle) (t*v₁) ∧
      (1/3:ℝ) ≤ dist (t*v₀ : UnitAddCircle) (t*v₂) := by
  simpa only [relative_distance] using
    two_real_speeds (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂)

/-- The complete three-runner case in the unit-circle metric, for arbitrary
distinct real speeds, including negative speeds and the stationary runner. -/
theorem three_runners (speed : Fin 3 ↪ ℝ) (r : Fin 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ s : Fin 3, s ≠ r →
      (1/3:ℝ) ≤ dist (t*speed r : UnitAddCircle) (t*speed s) := by
  fin_cases r
  · obtain ⟨t, ht, h₁, h₂⟩ := three_speeds
      (speed.injective.ne (by decide : (0:Fin 3) ≠ 1))
      (speed.injective.ne (by decide : (0:Fin 3) ≠ 2))
    refine ⟨t, ht, ?_⟩
    intro s hs
    fin_cases s <;> simp_all
  · obtain ⟨t, ht, h₁, h₂⟩ := three_speeds
      (speed.injective.ne (by decide : (1:Fin 3) ≠ 0))
      (speed.injective.ne (by decide : (1:Fin 3) ≠ 2))
    refine ⟨t, ht, ?_⟩
    intro s hs
    fin_cases s <;> simp_all
  · obtain ⟨t, ht, h₁, h₂⟩ := three_speeds
      (speed.injective.ne (by decide : (2:Fin 3) ≠ 0))
      (speed.injective.ne (by decide : (2:Fin 3) ≠ 1))
    refine ⟨t, ht, ?_⟩
    intro s hs
    fin_cases s <;> simp_all

/-- A sufficiently long time interval contains an entire safe interval for a
new positive speed. This is the interval-nesting step, not a sampling argument. -/
theorem insert_band {δ a b v : ℝ} (hv : 0 < v)
    (hhalf : δ ≤ 1/2) (hwidth : 2-2*δ ≤ (b-a)*v) :
    ∃ l u, a ≤ l ∧ u ≤ b ∧ l ≤ u ∧ u-l = (1-2*δ)/v ∧
      ∀ t, l ≤ t → t ≤ u → Safe δ (t*v) := by
  let z : ℤ := ⌈v*a-δ⌉
  have hzlo : v*a-δ ≤ (z:ℝ) := Int.le_ceil _
  have hzhi : (z:ℝ) < v*a-δ+1 := Int.ceil_lt_add_one _
  refine ⟨((z:ℝ)+δ)/v, ((z:ℝ)+1-δ)/v, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hv).mpr
    nlinarith
  · apply (div_le_iff₀ hv).mpr
    nlinarith
  · apply (div_le_div_iff_of_pos_right hv).mpr
    linarith
  · field_simp
    ring
  · intro t htlo hthi
    exact ⟨z, (div_le_iff₀ hv).mp htlo, (le_div_iff₀ hv).mp hthi⟩

/-- A finite initial segment of positive speeds has a common safe interval
when its consecutive ratios satisfy the stated sufficient condition. -/
theorem lacunary_band (v : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hv : ∀ i, 0 < v i)
    (hgap : ∀ i, (2-2*δ)*v i ≤ (1-2*δ)*v (i+1)) (n : ℕ) :
    ∃ l u, 0 < l ∧ l ≤ u ∧ u-l = (1-2*δ)/v n ∧
      ∀ i ≤ n, ∀ t, l ≤ t → t ≤ u → Safe δ (t*v i) := by
  induction n with
  | zero =>
    refine ⟨δ/v 0, (1-δ)/v 0, div_pos hδ (hv 0), ?_, ?_, ?_⟩
    · apply (div_le_div_iff_of_pos_right (hv 0)).mpr
      linarith
    · ring
    · intro i hi t htlo hthi
      have : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      refine ⟨0, ?_, ?_⟩ <;> simp only [Int.cast_zero, zero_add]
      · exact (div_le_iff₀ (hv 0)).mp htlo
      · exact (le_div_iff₀ (hv 0)).mp hthi
  | succ n ih =>
    obtain ⟨a, b, ha, hab, hwidth, hold⟩ := ih
    have hw : 2-2*δ ≤ (b-a)*v (n+1) := by
      rw [hwidth, div_mul_eq_mul_div]
      exact (le_div_iff₀ (hv n)).mpr (hgap n)
    obtain ⟨l, u, hal, hub, hlu, hul, hnew⟩ := insert_band (hv (n+1)) hhalf.le hw
    refine ⟨l, u, lt_of_lt_of_le ha hal, hlu, hul, ?_⟩
    intro i hi t hlt htu
    rcases Nat.le_succ_iff.mp hi with hi | hi
    · exact hold i hi t (hal.trans hlt) (htu.trans hub)
    · subst i
      exact hnew t hlt htu

/-- The interval construction yields a genuine common time for every finite
prefix, not merely a separate time for each speed. -/
theorem lacunary_speeds (v : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hv : ∀ i, 0 < v i)
    (hgap : ∀ i, (2-2*δ)*v i ≤ (1-2*δ)*v (i+1)) (n : ℕ) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ≤ n, δ ≤ ‖(t*v i : UnitAddCircle)‖ := by
  obtain ⟨l, u, hl, hlu, _, hs⟩ := lacunary_band v δ hδ hhalf hv hgap n
  exact ⟨l, hl, fun i hi => norm_ge_of_safe (hs i hi l le_rfl hlu)⟩

/-- A shorter safe interval can be retained even when a full unit-period
safe interval does not fit. -/
theorem safe_subinterval {δ w x y : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hws : w ≤ 1-2*δ)
    (hlen : 2*w+2*δ ≤ y-x) :
    ∃ l, x ≤ l ∧ l+w ≤ y ∧
      ∀ u, l ≤ u → u ≤ l+w → Safe δ u := by
  let z : ℤ := ⌊x-δ⌋
  have hzlo : (z:ℝ) ≤ x-δ := Int.floor_le _
  have hzhi : x-δ < (z:ℝ)+1 := Int.lt_floor_add_one _
  by_cases h : x+w ≤ (z:ℝ)+1-δ
  · refine ⟨x, le_rfl, ?_, ?_⟩
    · linarith
    · intro u hxu hux
      exact ⟨z, by linarith, by linarith⟩
  · refine ⟨(z:ℝ)+1+δ, by linarith, by linarith, ?_⟩
    intro u hlu hul
    refine ⟨z+1, ?_, ?_⟩ <;> push_cast <;> linarith

/-- Nested intervals with an explicit remaining length. Only velocities in
the finite prefix and their consecutive doubling inequalities are assumed. -/
theorem doubling_band (v : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (m k : ℕ) (hk : k ≤ m) (hsmall : ((m:ℝ)+2)*δ ≤ 1)
    (hv : ∀ i ≤ k, 0 < v i)
    (hgap : ∀ i < k, 2*v i ≤ v (i+1)) :
    ∃ l u, 0 < l ∧ l ≤ u ∧ (u-l)*v k = ((m:ℝ)-k)*δ ∧
      ∀ i ≤ k, ∀ t, l ≤ t → t ≤ u → Safe δ (t*v i) := by
  induction k with
  | zero =>
    have hv0 := hv 0 le_rfl
    refine ⟨δ/v 0, (δ+(m:ℝ)*δ)/v 0, div_pos hδ hv0, ?_, ?_, ?_⟩
    · apply (div_le_div_iff_of_pos_right hv0).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg m) hδ.le]
    · simp only [Nat.cast_zero, sub_zero]
      field_simp
      ring
    · intro i hi t htlo hthi
      have : i=0 := Nat.eq_zero_of_le_zero hi
      subst i
      have hlo := (div_le_iff₀ hv0).mp htlo
      have hhi := (le_div_iff₀ hv0).mp hthi
      exact ⟨0, by simpa, by simp only [Int.cast_zero, zero_add]; nlinarith⟩
  | succ k ih =>
    have hkm : k ≤ m := by omega
    obtain ⟨a,b,ha,hab,hw,hold⟩ := ih hkm
      (fun i hi => hv i (by omega)) (fun i hi => hgap i (by omega))
    let w : ℝ := ((m:ℝ)-(k+1))*δ
    have hcast : (k:ℝ)+1 ≤ m := by exact_mod_cast hk
    have hwpos : 0 ≤ w := by
      dsimp [w]
      exact mul_nonneg (by linarith) hδ.le
    have hwmax : w ≤ 1-2*δ := by
      dsimp [w]
      nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)+1 by positivity) hδ.le]
    have hlen : 2*w+2*δ ≤ b*v (k+1)-a*v (k+1) := by
      have hg := mul_le_mul_of_nonneg_left (hgap k (by omega)) (sub_nonneg.mpr hab)
      dsimp [w]
      nlinarith
    obtain ⟨c,hac,hcb,hnew⟩ := safe_subinterval hδ.le hwpos hwmax hlen
    have hvnext := hv (k+1) le_rfl
    have hal : a ≤ c/v (k+1) := (le_div_iff₀ hvnext).mpr hac
    have hub : (c+w)/v (k+1) ≤ b := (div_le_iff₀ hvnext).mpr hcb
    refine ⟨c/v (k+1), (c+w)/v (k+1), lt_of_lt_of_le ha hal, ?_, ?_, ?_⟩
    · apply (div_le_div_iff_of_pos_right hvnext).mpr
      linarith
    · simp only [Nat.cast_add, Nat.cast_one]
      dsimp [w]
      field_simp
      ring
    · intro i hi t htlo hthi
      rcases Nat.le_succ_iff.mp hi with hi | hi
      · exact hold i hi t (hal.trans htlo) (hthi.trans hub)
      · subst i
        exact hnew (t*v (k+1)) ((div_le_iff₀ hvnext).mp htlo)
          ((le_div_iff₀ hvnext).mp hthi)

/-- The known doubling-speed family: `m+1` positive relative velocities,
with every next speed at least twice the preceding one, meet the exact
lonely-runner threshold `1/(m+2)` at one common positive time. -/
theorem doubling_speeds (v : ℕ → ℝ) (m : ℕ)
    (hv : ∀ i ≤ m, 0 < v i) (hgap : ∀ i < m, 2*v i ≤ v (i+1)) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ≤ m,
      1/((m:ℝ)+2) ≤ ‖(t*v i : UnitAddCircle)‖ := by
  obtain ⟨l,u,hl,hlu,_,hs⟩ := doubling_band v (1/((m:ℝ)+2))
    (by positivity) m m le_rfl (by field_simp; norm_num) hv hgap
  exact ⟨l,hl,fun i hi => norm_ge_of_safe (hs i hi l le_rfl hlu)⟩

/-- Signs are irrelevant for distances from the reference runner. -/
theorem doubling_real_speeds (v : ℕ → ℝ) (m : ℕ)
    (hv : ∀ i ≤ m, v i ≠ 0) (hgap : ∀ i < m, 2*|v i| ≤ |v (i+1)|) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ≤ m,
      1/((m:ℝ)+2) ≤ ‖(t*v i : UnitAddCircle)‖ := by
  obtain ⟨t,ht,hs⟩ := doubling_speeds (fun i => |v i|) m
    (fun i hi => abs_pos.mpr (hv i hi)) hgap
  exact ⟨t,ht,fun i hi => (norm_abs_speed t (v i)) ▸ hs i hi⟩

/-- Direct circle-metric version for an arbitrary reference runner and any
finite list of other runners, ordered by doubling absolute relative speeds. -/
theorem doubling_relative_to_runner (v₀ : ℝ) (v : ℕ → ℝ) (m : ℕ)
    (hv : ∀ i ≤ m, v i ≠ v₀)
    (hgap : ∀ i < m, 2*|v i-v₀| ≤ |v (i+1)-v₀|) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ≤ m,
      1/((m:ℝ)+2) ≤ dist (t*v i : UnitAddCircle) (t*v₀) := by
  simpa only [relative_distance] using
    doubling_real_speeds (fun i => v i-v₀) m
      (fun i hi => sub_ne_zero.mpr (hv i hi)) hgap

/-- Original running-track formulation. The list `other 0, ..., other m`
covers the other runners in increasing absolute relative-speed order. -/
theorem doubling_runners (m : ℕ) (speed : Fin (m+2) ↪ ℝ) (r : Fin (m+2))
    (other : ℕ → Fin (m+2))
    (hother : ∀ i ≤ m, other i ≠ r)
    (hcover : ∀ s, s ≠ r → ∃ i ≤ m, other i = s)
    (hgap : ∀ i < m,
      2*|speed (other i)-speed r| ≤ |speed (other (i+1))-speed r|) :
    ∃ t : ℝ, 0 < t ∧ ∀ s, s ≠ r →
      1/((m:ℝ)+2) ≤ dist (t*speed r : UnitAddCircle) (t*speed s) := by
  obtain ⟨t,ht,hs⟩ := doubling_relative_to_runner (speed r)
    (fun i => speed (other i)) m
    (fun i hi => speed.injective.ne (hother i hi)) hgap
  refine ⟨t,ht,?_⟩
  intro s hsr
  obtain ⟨i,hi,rfl⟩ := hcover s hsr
  simpa only [dist_comm] using hs i hi

/-- An adapter to the three-runner statement's user-supplied `lonely` predicate,
with the same circle metric, threshold, and nonnegative-time conclusion. -/
theorem three_runners_spec (speed : Fin 3 ↪ ℝ) (lonely : Fin 3 → ℝ → Prop)
    (lonely_def : ∀ r t, lonely r t ↔ ∀ s : Fin 3, s ≠ r →
      dist (t*speed r : UnitAddCircle) (t*speed s) ≥ 1/3) (r : Fin 3) :
    ∃ t ≥ (0:ℝ), lonely r t := by
  obtain ⟨t,ht,hs⟩ := three_runners speed r
  exact ⟨t,ht.le,(lonely_def r t).mpr hs⟩

end JSP000017
