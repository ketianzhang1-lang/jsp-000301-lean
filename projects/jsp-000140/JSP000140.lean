/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Prepared with OpenAI ChatGPT assistance.
JSP-000140 / Erdos 136: the classical lower bound for (4,5)-colorings.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

open Finset
namespace JSP000140

variable {n k : ℕ}
abbrev Coloring (n k : ℕ) := Fin n → Fin n → Fin k

def Colors4 (χ : Coloring n k) (a b c d : Fin n) : Finset (Fin k) :=
  {χ a b, χ a c, χ a d, χ b c, χ b d, χ c d}

def Admissible (χ : Coloring n k) : Prop :=
  (∀ a b, χ a b = χ b a) ∧
  ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    5 ≤ (Colors4 χ a b c d).card

def Fork (χ : Coloring n k) (v a b : Fin n) : Prop :=
  v ≠ a ∧ v ≠ b ∧ a ≠ b ∧ χ v a = χ v b

lemma card_le_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a,b,c,d} : Finset α).card ≤ 4 := by
  have h := card_insert_le a ({b,c,d} : Finset α)
  have h' := card_insert_le b ({c,d} : Finset α)
  have h'' := card_insert_le c ({d} : Finset α)
  simp only [card_singleton] at h''
  omega

lemma bad_quad (χ : Coloring n k) (hχ : Admissible χ)
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (s : Finset (Fin k)) (hs : s.card ≤ 4) (hsub : Colors4 χ a b c d ⊆ s) : False := by
  have h := hχ.2 a b c d hab hac had hbc hbd hcd
  have := card_le_card hsub
  omega

lemma triangle_not_mono (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ)
    {v a b : Fin n} (hv : Fork χ v a b) : χ v a ≠ χ a b := by
  intro he
  have hcard : ({v,a,b} : Finset (Fin n)).card < (univ : Finset (Fin n)).card := by
    have h1 := card_insert_le v ({a,b} : Finset (Fin n))
    have h2 := card_insert_le a ({b} : Finset (Fin n))
    simp only [card_singleton, card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨d, _, hd⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hdv : v ≠ d := by intro h; subst d; simp at hd
  have hda : a ≠ d := by intro h; subst d; simp at hd
  have hdb : b ≠ d := by intro h; subst d; simp at hd
  apply bad_quad χ hχ v a b d hv.1 hv.2.1 hdv hv.2.2.1 hda hdb
    {χ v a,χ v d,χ a d,χ b d} (card_le_four ..)
  intro x hx
  simp only [Colors4, mem_insert, mem_singleton] at hx ⊢
  have hcolor := hv.2.2.2
  rcases hx with h|h|h|h|h|h <;> aesop

lemma fork_center_unique (χ : Coloring n k) (hχ : Admissible χ)
    {v a b d : Fin n} (h : Fork χ v a b) (h' : Fork χ v a d) : b = d := by
  by_contra hbd
  have hcolor2 := h'.2.2.2
  apply bad_quad χ hχ v a b d h.1 h.2.1 h'.2.1 h.2.2.1 h'.2.2.1 hbd
    {χ v a,χ a b,χ a d,χ b d} (card_le_four ..)
  intro x hx
  simp only [Colors4, mem_insert, mem_singleton] at hx ⊢
  have hcolor := h.2.2.2
  rcases hx with hx|hx|hx|hx|hx|hx <;> aesop

lemma fork_swap {χ : Coloring n k} {v a b : Fin n} (h : Fork χ v a b) :
    Fork χ v b a := ⟨h.2.1,h.1,h.2.2.1.symm,h.2.2.2.symm⟩

lemma fork_centers_not_adjacent (hn : 4 ≤ n) (χ : Coloring n k)
    (hχ : Admissible χ) {v a b d : Fin n} (h : Fork χ v a b)
    (h' : Fork χ a v d) : False := by
  by_cases hbd : b = d
  · subst d
    exact triangle_not_mono hn χ hχ h (by rw [hχ.1 v a]; exact h'.2.2.2)
  apply bad_quad χ hχ v a b d h.1 h.2.1 h'.2.2.1 h.2.2.1 h'.2.1 hbd
    {χ v a,χ v d,χ a b,χ b d} (card_le_four ..)
  intro x hx
  have he : χ v a = χ a d := (hχ.1 v a).trans h'.2.2.2
  simp only [Colors4, mem_insert, mem_singleton] at hx ⊢
  have hcolor := h.2.2.2
  rcases hx with hx|hx|hx|hx|hx|hx <;> aesop

lemma fork_closing_isolated (hn : 4 ≤ n) (χ : Coloring n k)
    (hχ : Admissible χ) {v a b d : Fin n} (h : Fork χ v a b)
    (had : a ≠ d) (hbd : b ≠ d) : χ a b ≠ χ a d := by
  intro he
  by_cases hvd : v = d
  · subst d
    exact triangle_not_mono hn χ hχ h ((he.trans (hχ.1 a v)).symm)
  apply bad_quad χ hχ v a b d h.1 h.2.1 hvd h.2.2.1 had hbd
    {χ v a,χ v d,χ a b,χ b d} (card_le_four ..)
  intro x hx
  simp only [Colors4, mem_insert, mem_singleton] at hx ⊢
  have hcolor := h.2.2.2
  rcases hx with hx|hx|hx|hx|hx|hx <;> aesop

lemma fork_closing_unique (χ : Coloring n k) (hχ : Admissible χ)
    {v w a b : Fin n} (h : Fork χ v a b) (h' : Fork χ w a b) : v = w := by
  by_contra hvw
  apply bad_quad χ hχ a b v w h.2.2.1 h.1.symm h'.1.symm
    h.2.1.symm h'.2.1.symm hvw {χ a b,χ a v,χ a w,χ v w} (card_le_four ..)
  intro x hx
  have hbv : χ b v = χ a v := by rw [hχ.1 b v, hχ.1 a v]; exact h.2.2.2.symm
  have hbw : χ b w = χ a w := by rw [hχ.1 b w, hχ.1 a w]; exact h'.2.2.2.symm
  simp only [Colors4, mem_insert, mem_singleton] at hx ⊢
  have hcolor := h.2.2.2
  rcases hx with hx|hx|hx|hx|hx|hx <;> aesop

instance (χ : Coloring n k) (v a b : Fin n) : Decidable (Fork χ v a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

abbrev ForkType (χ : Coloring n k) :=
  {t : Fin n × Fin n × Fin n // Fork χ t.1 t.2.1 t.2.2}

def edgeImage (χ : Coloring n k) (p : ForkType χ × Fin 3) : Fin n × Fin n :=
  ![(p.1.val.1,p.1.val.2.1), (p.1.val.2.1,p.1.val.2.2),
    (p.1.val.2.2,p.1.val.1)] p.2

lemma edgeImage_injective (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ) :
    Function.Injective (edgeImage χ) := by
  rintro ⟨⟨⟨v,a,b⟩,h⟩,i⟩ ⟨⟨⟨w,c,d⟩,h'⟩,j⟩ he
  change Fork χ v a b at h
  change Fork χ w c d at h'
  fin_cases i <;> fin_cases j <;> simp only [edgeImage] at he
  · obtain ⟨rfl,rfl⟩ := he
    have := fork_center_unique χ hχ h h'
    subst d
    rfl
  · obtain ⟨rfl,rfl⟩ := he
    exact (fork_closing_isolated hn χ hχ h' h.2.1 h.2.2.1 h.2.2.2).elim
  · obtain ⟨rfl,rfl⟩ := he
    exact (fork_centers_not_adjacent hn χ hχ h (fork_swap h')).elim
  · obtain ⟨rfl,rfl⟩ := he
    exact (fork_closing_isolated hn χ hχ h h'.2.1 h'.2.2.1 h'.2.2.2).elim
  · obtain ⟨rfl,rfl⟩ := he
    have := fork_closing_unique χ hχ h h'
    subst w
    rfl
  · obtain ⟨rfl,rfl⟩ := he
    exact (fork_closing_isolated hn χ hχ (fork_swap h)
      h'.1 h'.2.2.1.symm h'.2.2.2.symm).elim
  · obtain ⟨rfl,rfl⟩ := he
    exact (fork_centers_not_adjacent hn χ hχ (fork_swap h) h').elim
  · obtain ⟨rfl,rfl⟩ := he
    exact (fork_closing_isolated hn χ hχ (fork_swap h')
      h.1 h.2.2.1.symm h.2.2.2.symm).elim
  · obtain ⟨rfl,rfl⟩ := he
    have := fork_center_unique χ hχ (fork_swap h) (fork_swap h')
    subst c
    rfl

lemma edgeImage_mem (χ : Coloring n k) (p : ForkType χ × Fin 3) :
    edgeImage χ p ∈ (univ : Finset (Fin n)).offDiag := by
  rcases p with ⟨⟨⟨v,a,b⟩,h⟩,i⟩
  change Fork χ v a b at h
  fin_cases i <;> simp [edgeImage, h.1, h.2.2.1, Ne.symm h.2.1]

/-- The three directed edges per ordered fork are all different. -/
lemma fork_packing (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ) :
    3 * Fintype.card (ForkType χ) ≤ n * (n-1) := by
  let f : ForkType χ × Fin 3 → ↥((univ : Finset (Fin n)).offDiag) :=
    fun p => ⟨edgeImage χ p, edgeImage_mem χ p⟩
  have hf : Function.Injective f := by
    intro x y h
    exact edgeImage_injective hn χ hχ (congrArg Subtype.val h)
  have := Fintype.card_le_of_injective f hf
  have hc : Fintype.card ↥((univ : Finset (Fin n)).offDiag) = n*(n-1) := by
    rw [Fintype.card_coe, offDiag_card]
    simp [Nat.mul_sub_left_distrib]
  rw [Fintype.card_prod, Fintype.card_fin, hc] at this
  simpa [Nat.mul_comm] using this

def neighbors (χ : Coloring n k) (v : Fin n) (c : Fin k) : Finset (Fin n) :=
  univ.filter fun w => v ≠ w ∧ χ v w = c

abbrev FiberFork (χ : Coloring n k) :=
  Σ v : Fin n, Σ c : Fin k, ↥((neighbors χ v c).offDiag)

def forkEquiv (χ : Coloring n k) : ForkType χ ≃ FiberFork χ where
  toFun p := ⟨p.val.1, χ p.val.1 p.val.2.1,
    ⟨(p.val.2.1,p.val.2.2), mem_offDiag.mpr
      ⟨by simp [neighbors, p.property.1],
       by simp [neighbors, p.property.2.1, p.property.2.2.2], p.property.2.2.1⟩⟩⟩
  invFun p := ⟨(p.1,p.2.2.val.1,p.2.2.val.2), by
    obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp p.2.2.property
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    exact ⟨ha'.1,hb'.1,hab,ha'.2.trans hb'.2.symm⟩⟩
  left_inv := by rintro ⟨⟨v,a,b⟩,h⟩; rfl
  right_inv := by
    rintro ⟨v,c,⟨⟨a,b⟩,h⟩⟩
    have he := (mem_filter.mp (mem_offDiag.mp h).1).2.2
    change χ v a = c at he
    subst c
    rfl

lemma fork_card_eq (χ : Coloring n k) :
    Fintype.card (ForkType χ) =
      ∑ v : Fin n, ∑ c : Fin k,
        (neighbors χ v c).card * ((neighbors χ v c).card - 1) := by
  rw [Fintype.card_congr (forkEquiv χ)]
  simp only [FiberFork, Fintype.card_sigma, Fintype.card_coe, offDiag_card,
    Nat.mul_sub_left_distrib, Nat.mul_one]

lemma sum_degree (χ : Coloring n k) (v : Fin n) :
    ∑ c : Fin k, (neighbors χ v c).card = n - 1 := by
  have he (c : Fin k) :
      ((univ.erase v).filter (fun w => χ v w = c)) = neighbors χ v c := by
    ext w
    simp [neighbors, ne_comm]
  have h := sum_card_fiberwise_eq_card_filter (univ.erase v) (univ : Finset (Fin k)) (χ v)
  simp only [he] at h
  simpa using h

lemma quadratic_degree_bound (d : ℕ) : 2*d ≤ 2+d*(d-1) := by
  rcases d with _ | d
  · simp
  · simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (d*d)]

lemma incidence_bound (χ : Coloring n k) :
    2*n*(n-1) ≤ 2*n*k + Fintype.card (ForkType χ) := by
  have hv (v : Fin n) :
      2*(n-1) ≤ 2*k + ∑ c : Fin k,
        (neighbors χ v c).card * ((neighbors χ v c).card-1) := by
    have h := sum_le_sum (s := (univ : Finset (Fin k)))
      (fun c _ => quadratic_degree_bound (neighbors χ v c).card)
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, sum_degree] at h
    simpa only [Nat.mul_comm k 2] using h
  have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun v _ => hv v)
  rw [fork_card_eq]
  simpa [sum_add_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Classical 5/6 lower bound, for every admissible finite coloring. -/
theorem lower_bound (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ) :
    5*(n-1) ≤ 6*k := by
  have hp := fork_packing hn χ hχ
  have hi := incidence_bound χ
  have : n*(5*(n-1)) ≤ n*(6*k) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this (by omega)

lemma fork_absent_color (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ)
    {v a b : Fin n} (h : Fork χ v a b) : neighbors χ v (χ a b) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hw' := (mem_filter.mp hw).2
  by_cases haw : a = w
  · subst w
    exact triangle_not_mono hn χ hχ h hw'.2
  by_cases hbw : b = w
  · subst w
    exact triangle_not_mono hn χ hχ h (h.2.2.2.trans hw'.2)
  apply bad_quad χ hχ v a b w h.1 h.2.1 hw'.1 h.2.2.1 haw hbw
    {χ v a,χ a b,χ a w,χ b w} (card_le_four ..)
  intro x hx
  have hcolor := h.2.2.2
  simp only [Colors4, mem_insert, mem_singleton] at hx ⊢
  rcases hx with hx|hx|hx|hx|hx|hx <;> aesop

lemma strict_incidence_bound (χ : Coloring n k)
    {v : Fin n} {c : Fin k} (hzero : neighbors χ v c = ∅) :
    2*n*(n-1) < 2*n*k + Fintype.card (ForkType χ) := by
  have hall (w : Fin n) :
      2*(n-1) ≤ 2*k + ∑ d : Fin k,
        (neighbors χ w d).card * ((neighbors χ w d).card-1) := by
    have h := sum_le_sum (s := (univ : Finset (Fin k)))
      (fun d _ => quadratic_degree_bound (neighbors χ w d).card)
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, sum_degree] at h
    simpa only [Nat.mul_comm k 2] using h
  have hv : 2*(n-1) < 2*k + ∑ d : Fin k,
      (neighbors χ v d).card * ((neighbors χ v d).card-1) := by
    have h := sum_lt_sum (s := (univ : Finset (Fin k)))
      (fun d _ => quadratic_degree_bound (neighbors χ v d).card)
      ⟨c, mem_univ c, by simp [hzero]⟩
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, sum_degree] at h
    simpa only [Nat.mul_comm k 2] using h
  have h := sum_lt_sum (s := (univ : Finset (Fin n))) (fun w _ => hall w)
    ⟨v, mem_univ v, hv⟩
  rw [fork_card_eq]
  simpa [sum_add_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Equality in the classical lower bound is impossible for n >= 4. -/
theorem strict_lower_bound (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ) :
    5*(n-1) < 6*k := by
  have hp := fork_packing hn χ hχ
  by_cases hF : Fintype.card (ForkType χ) = 0
  · have hi := incidence_bound χ
    rw [hF] at hi
    have hn0 : 0 < n := by omega
    have hn1 : 0 < n-1 := by omega
    nlinarith
  · obtain ⟨p⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hF)
    have hz := fork_absent_color hn χ hχ p.property
    have hi := strict_incidence_bound χ hz
    have : n*(5*(n-1)) < n*(6*k) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this

/-- Exact integer rounding of the strict lower bound. -/
theorem integer_lower_bound (hn : 4 ≤ n) (χ : Coloring n k) (hχ : Admissible χ) :
    5*(n-1)/6 + 1 ≤ k := by
  have := strict_lower_bound hn χ hχ
  omega

/-- Colors on genuine edges of a vertex subset; diagonal values are ignored. -/
def edgeColors (χ : Coloring n k) (S : Finset (Fin n)) : Finset (Fin k) :=
  S.offDiag.image fun p => χ p.1 p.2

lemma edgeColors_four (χ : Coloring n k) (hsym : ∀ a b, χ a b = χ b a)
    {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    edgeColors χ {a,b,c,d} = Colors4 χ a b c d := by
  ext x
  simp only [edgeColors, mem_image, mem_offDiag, mem_insert, mem_singleton, Colors4]
  constructor
  · rintro ⟨⟨v,w⟩,⟨hv,hw,hvw⟩,he⟩
    dsimp only at hv hw hvw he
    rcases hv with rfl|rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl|rfl <;>
      simp_all
  · intro hx
    rcases hx with h|h|h|h|h|h
    · exact ⟨(a,b),⟨by simp,by simp,hab⟩,h.symm⟩
    · exact ⟨(a,c),⟨by simp,by simp,hac⟩,h.symm⟩
    · exact ⟨(a,d),⟨by simp,by simp,had⟩,h.symm⟩
    · exact ⟨(b,c),⟨by simp,by simp,hbc⟩,h.symm⟩
    · exact ⟨(b,d),⟨by simp,by simp,hbd⟩,h.symm⟩
    · exact ⟨(c,d),⟨by simp,by simp,hcd⟩,h.symm⟩

/-- Standard statement: every four-element subset sees at least five colors. -/
theorem lower_bound_from_vertex_sets (hn : 4 ≤ n) (χ : Coloring n k)
    (hsym : ∀ a b, χ a b = χ b a)
    (hsets : ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ (edgeColors χ S).card) :
    5*(n-1)/6+1 ≤ k := by
  apply integer_lower_bound hn χ
  refine ⟨hsym, ?_⟩
  intro a b c d hab hac had hbc hbd hcd
  have hc : ({a,b,c,d} : Finset (Fin n)).card = 4 := by
    simp [hab,hac,had,hbc,hbd,hcd]
  have h := hsets {a,b,c,d} hc
  rw [edgeColors_four χ hsym hab hac had hbc hbd hcd] at h
  exact h

end JSP000140
