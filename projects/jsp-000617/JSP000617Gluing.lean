import JSP000617Packet
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.LiminfLimsup

/-! Separation and short-interval sparsity control all cross-scale sums. -/
namespace JSP000617

lemma natReps_mono {A B C D : Finset ℕ} (hAC : A ⊆ C) (hBD : B ⊆ D) (n : ℕ) :
    natReps A B n ⊆ natReps C D n := by
  intro ab hab
  obtain ⟨hab,he⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hAC ha,hBD hb⟩,he⟩

lemma natSums_mono {A B : Finset ℕ} (h : A ⊆ B) : natSums A ⊆ natSums B :=
  Finset.image_subset_image (Finset.product_subset_product h h)

lemma natReps_swap (A B : Finset ℕ) (n : ℕ) :
    (natReps A B n).card = (natReps B A n).card := by
  have he : (natReps A B n).image Prod.swap = natReps B A n := by
    ext ab
    simp only [natReps,Finset.mem_image,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨a,b⟩,⟨⟨ha,hb⟩,he⟩,rfl⟩
      exact ⟨⟨hb,ha⟩,by simpa [Prod.swap,Nat.add_comm] using he⟩
    · rintro ⟨⟨ha,hb⟩,he⟩
      exact ⟨ab.swap,⟨⟨hb,ha⟩,by simpa [Nat.add_comm] using he⟩,rfl⟩
  rw [←he,Finset.card_image_of_injective _ Prod.swap_injective]

lemma cross_reps_le {B Q : Finset ℕ} {d C : ℕ}
    (hB : ∀ b ∈ B, b ≤ d) (hQ : locallySparse Q d C) (n : ℕ) :
    (natReps B Q n).card ≤ C := by
  let S := (natReps B Q n).image Prod.snd
  have hinj : Set.InjOn Prod.snd (↑(natReps B Q n) : Set (ℕ × ℕ)) := by
    rintro ⟨a,b⟩ hab ⟨c,e⟩ hce he
    have h1 := (Finset.mem_filter.mp hab).2
    have h2 := (Finset.mem_filter.mp hce).2
    apply Prod.ext <;> dsimp at * <;> omega
  have hsub : S ⊆ Q := by
    intro x hx
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2
  have hdiam : smallDiameter S d := by
    intro x hx y hy
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨c,e⟩,hce,rfl⟩ := Finset.mem_image.mp hy
    have h1 := (Finset.mem_filter.mp hab).2
    have h2 := (Finset.mem_filter.mp hce).2
    have hc := hB c (Finset.mem_product.mp (Finset.mem_filter.mp hce).1).1
    dsimp at *
    omega
  have hc := hQ S hsub hdiam
  simpa [S,Finset.card_image_of_injOn hinj] using hc

lemma natReps_union_le (B Q : Finset ℕ) (n : ℕ) :
    (natReps (B ∪ Q) (B ∪ Q) n).card ≤
      (natReps B B n).card + (natReps B Q n).card +
      (natReps Q B n).card + (natReps Q Q n).card := by
  have hsub : natReps (B ∪ Q) (B ∪ Q) n ⊆
      ((natReps B B n ∪ natReps B Q n) ∪ natReps Q B n) ∪ natReps Q Q n := by
    intro ab hab
    simp only [natReps,Finset.mem_filter,Finset.mem_product,Finset.mem_union] at *
    aesop
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (natReps B B n) (natReps B Q n)
  have h3 := Finset.card_union_le (natReps B B n ∪ natReps B Q n) (natReps Q B n)
  have h4 := Finset.card_union_le
    ((natReps B B n ∪ natReps B Q n) ∪ natReps Q B n) (natReps Q Q n)
  omega

/-- Extending a bounded set by a distant sparse packet preserves a fixed bound. -/
theorem separated_extension {B Q : Finset ℕ} {d t R C H : ℕ}
    (hB : ∀ b ∈ B, b ≤ d) (ht : 2*d < t)
    (hQmin : ∀ q ∈ Q, t ≤ q)
    (hQ : locallySparse Q d C)
    (hR : ∀ n, (natReps Q Q n).card ≤ R)
    (hH : ∀ n, (natReps B B n).card ≤ H)
    (hRC : R+2*C ≤ H) :
    ∀ n, (natReps (B ∪ Q) (B ∪ Q) n).card ≤ H := by
  intro n
  by_cases hn : n < t
  · have he : natReps (B ∪ Q) (B ∪ Q) n = natReps B B n := by
      apply Finset.Subset.antisymm
      · intro ab hab
        obtain ⟨hab,he⟩ := Finset.mem_filter.mp hab
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
        have hna : ab.1 ∉ Q := by intro h; have := hQmin _ h; omega
        have hnb : ab.2 ∉ Q := by intro h; have := hQmin _ h; omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(Finset.mem_union.mp ha).resolve_right hna,
           (Finset.mem_union.mp hb).resolve_right hnb⟩,he⟩
      · exact natReps_mono Finset.subset_union_left Finset.subset_union_left n
    rw [he]
    exact hH n
  · have he : natReps B B n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ab hab
      obtain ⟨hab,he⟩ := Finset.mem_filter.mp hab
      have ha := hB ab.1 (Finset.mem_product.mp hab).1
      have hb := hB ab.2 (Finset.mem_product.mp hab).2
      omega
    have hcross := cross_reps_le hB hQ n
    have hswap := natReps_swap Q B n
    have htotal := natReps_union_le B Q n
    rw [he,Finset.card_empty] at htotal
    have := hR n
    omega

end JSP000617
