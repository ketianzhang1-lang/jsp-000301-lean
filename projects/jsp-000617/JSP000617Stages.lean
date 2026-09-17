import JSP000617Gluing

namespace JSP000617

def uniformBound (m : ℕ) : ℕ := (2^m)^2*(8*(m+1)^2) + 2*((2^m)*(12*(m+1)))

def finitePrefixSums (B : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (natSums B).filter (fun s => s < N)

lemma locallySparse_mono {A : Finset ℕ} {d e C : ℕ} (h : d ≤ e)
    (hA : locallySparse A e C) : locallySparse A d C := by
  intro S hS hdiam
  apply hA S hS
  intro x hx y hy
  exact (hdiam x hx y hy).trans (Nat.add_le_add_left h y)

/-- One extension retains the uniform bound and creates a dense prefix beyond any threshold. -/
theorem dense_extension (m : ℕ) (hK : 4 ≤ 2^m) (B : Finset ℕ) (N₀ : ℕ)
    (hB : ∀ n, (natReps B B n).card ≤ uniformBound m) :
    ∃ D : Finset ℕ, B ⊆ D ∧
      (∀ n, (natReps D D n).card ≤ uniformBound m) ∧
      ∃ N, N₀ ≤ N ∧ 0 < N ∧
        (2^m-3)*N ≤ (2^m)*(finitePrefixSums D N).card := by
  let d := B.sup id
  let t := 2*d+1
  obtain ⟨p,hpge,hp⟩ := Nat.exists_infinite_primes (t+N₀+3)
  have hp2 : 2 < p := by omega
  have hdp : d ≤ p := by dsimp [t] at hpge; omega
  obtain ⟨Q,hQ,hcov,hR,hC⟩ := natural_packet hp hp2 m hK
  let L := (2^m)*(2*p*p)
  let T := natTranslate Q t
  let D := B ∪ T
  let N := 2*(t+L)
  have hd : ∀ b ∈ B, b ≤ d := by
    intro b hb
    exact Finset.le_sup (f:=id) hb
  have hTmin : ∀ q ∈ T, t ≤ q := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    omega
  have hTsparse : locallySparse T d ((2^m)*(12*(m+1))) :=
    locallySparse_mono hdp (locallySparse_translate hC t)
  have hTR : ∀ n, (natReps T T n).card ≤ (2^m)^2*(8*(m+1)^2) := by
    intro n
    exact (natReps_translate_le Q Q t t n).trans (hR _)
  have hD : ∀ n, (natReps D D n).card ≤ uniformBound m :=
    separated_extension hd (by dsimp [t]; omega) hTmin hTsparse hTR hB (by rfl)
  have hNL : L > 0 := by dsimp [L]; positivity
  have hN₀ : N₀ ≤ N := by
    have hpL : p ≤ L := by
      have hp1 : 1 ≤ p := hp.pos
      have hk1 : 1 ≤ 2^m := by omega
      have hpp : p ≤ 2*p*p := by nlinarith
      exact hpp.trans (by simpa [L] using Nat.mul_le_mul_right (2*p*p) hk1)
    dsimp [N]
    omega
  have hTN : ∀ a ∈ T, a < t+L := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have := hQ b hb
    change t+b < t+L
    omega
  have hsub : natSums T ⊆ finitePrefixSums D N := by
    intro s hs
    exact Finset.mem_filter.mpr
      ⟨natSums_mono Finset.subset_union_right hs,natSums_bound hTN hs⟩
  have hc := Finset.card_le_card hsub
  have hcard : (natSums T).card = (natSums Q).card := natSums_translate_card Q t
  rw [hcard] at hc
  have hc' := Nat.mul_le_mul_left (2^m) hc
  have hshift : (2^m-3)*t ≤ L := by
    have ht : t ≤ p := by omega
    have hp1 : 1 ≤ p := hp.pos
    have ht2 : t ≤ 2*p*p := by nlinarith
    have h1 := Nat.mul_le_mul_left (2^m-3) ht2
    have h2 := Nat.mul_le_mul_right (2*p*p) (Nat.sub_le (2^m) 3)
    exact h1.trans h2
  refine ⟨D,Finset.subset_union_left,hD,N,hN₀,by dsimp [N]; omega,?_⟩
  have hk2 : (2^m-2)+2=2^m := by omega
  have hk3 : (2^m-3)+3=2^m := by omega
  have hcov' : (2^m)*(natSums Q).card ≥ (2^m-2)*(2*L) := by
    simpa [L,Nat.mul_assoc] using hcov
  change (2^m-3)*(2*(t+L)) ≤ (2^m)*(finitePrefixSums D N).card
  have hfactor : (2^m-3)+1=2^m-2 := by omega
  rw [←hfactor] at hcov'
  nlinarith only [hcov',hc',hshift]

structure BoundedStage (m : ℕ) where
  points : Finset ℕ
  bound : ∀ n, (natReps points points n).card ≤ uniformBound m

noncomputable def nextStage (m : ℕ) (hK : 4 ≤ 2^m) (j : ℕ) (S : BoundedStage m) :
    BoundedStage m :=
  ⟨(dense_extension m hK S.points j S.bound).choose,
   (dense_extension m hK S.points j S.bound).choose_spec.2.1⟩

noncomputable def stages (m : ℕ) (hK : 4 ≤ 2^m) : ℕ → BoundedStage m
  | 0 => ⟨∅,by intro n; simp [natReps]⟩
  | j+1 => nextStage m hK j (stages m hK j)

theorem stages_step (m : ℕ) (hK : 4 ≤ 2^m) (j : ℕ) :
    (stages m hK j).points ⊆ (stages m hK (j+1)).points :=
  (dense_extension m hK (stages m hK j).points j (stages m hK j).bound).choose_spec.1

theorem stages_dense (m : ℕ) (hK : 4 ≤ 2^m) (j : ℕ) :
    ∃ N, j ≤ N ∧ 0 < N ∧
      (2^m-3)*N ≤ (2^m)*(finitePrefixSums (stages m hK (j+1)).points N).card :=
  (dense_extension m hK (stages m hK j).points j (stages m hK j).bound).choose_spec.2.2

theorem stages_mono (m : ℕ) (hK : 4 ≤ 2^m) :
    Monotone (fun j => (stages m hK j).points) :=
  monotone_nat_of_le_succ (stages_step m hK)

end JSP000617
