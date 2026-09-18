import JSP000388
import ErdosProblems.Erdos477

/-!
We integrate the attributed sixth-power existence proof with our separately
implemented quadratic obstruction. We also prove a general translation law
and obtain every integer translate of the sixth-power value set.
The upstream existence proof is credited in PROVENANCE.md and UPSTREAM.json.
-/

namespace JSP000388

/-- Our pair-value uniqueness predicate agrees exactly with the upstream one. -/
theorem exactComplement_iff_tiling (A : Set ℤ) (f : ℤ → ℤ) :
    ExactComplement A f ↔ Erdos477.IsTiling A (Set.range f) := Iff.rfl

/-- Translating polynomial values translates the complement in the opposite direction. -/
theorem exactComplement_translate {A : Set ℤ} {f : ℤ → ℤ}
    (h : ExactComplement A f) (c : ℤ) :
    ExactComplement ((fun a => a-c) '' A) (fun x => f x+c) := by
  intro z
  obtain ⟨p,hp,hu⟩ := h z
  refine ⟨(p.1-c,p.2+c),?_,?_⟩
  · refine ⟨⟨p.1,hp.1,rfl⟩,?_,by dsimp; omega⟩
    obtain ⟨x,hx⟩ := hp.2.1
    exact ⟨x,by simp [hx]⟩
  · intro q hq
    obtain ⟨a,ha,haq⟩ := hq.1
    obtain ⟨x,hx⟩ := hq.2.1
    dsimp at hx
    have heq : (q.1+c,q.2-c) = p := by
      apply hu
      refine ⟨?_,⟨x,by dsimp; omega⟩,by dsimp; omega⟩
      simpa [← haq] using ha
    have hleft := congrArg Prod.fst heq
    have hright := congrArg Prod.snd heq
    apply Prod.ext <;> dsimp at * <;> omega

/-- The complete positive existence witness, using the attributed upstream proof. -/
theorem exists_sixth_power_complement :
    ∃ A : Set ℤ, ExactComplement A (fun x : ℤ => x^6) :=
  Erdos477.erdos477_sixth_power

/-- Our translation consequence holds uniformly for every integer constant. -/
theorem exists_shifted_sixth_power_complement (c : ℤ) :
    ∃ A : Set ℤ, ExactComplement A (fun x : ℤ => x^6+c) := by
  obtain ⟨A,hA⟩ := exists_sixth_power_complement
  exact ⟨(fun a => a-c) '' A,exactComplement_translate hA c⟩

/-- Evaluation of the actual integer polynomial, rather than an abstract value set. -/
theorem exists_shifted_polynomial_complement (c : ℤ) :
    ∃ A : Set ℤ, ExactComplement A
      (fun x => (Polynomial.X^6+Polynomial.C c : Polynomial ℤ).eval x) := by
  simpa only [Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_C] using exists_shifted_sixth_power_complement c

/-- The literal original existence question, including polynomial degree and
uniqueness of the pair of summand VALUES, not of polynomial inputs. -/
theorem jsp_000388 :
    ∃ f : Polynomial ℤ, 2 ≤ f.degree ∧ ∃ A : Set ℤ,
      ∀ z : ℤ, ∃! p ∈ A ×ˢ (Set.range f.eval), z = p.1+p.2 := by
  obtain ⟨A,hA⟩ := exists_sixth_power_complement
  refine ⟨Polynomial.X^6,by norm_num,A,?_⟩
  intro z
  simpa only [Polynomial.eval_pow,Polynomial.eval_X,Set.mem_prod,and_assoc,
    eq_comm] using hA z

/-- A single interface combines the complete existence result with our
independent obstruction for every normalized quadratic, including b=0. -/
theorem existence_and_quadratic_obstruction :
    (∃ A : Set ℤ, ExactComplement A (fun x : ℤ => x^6)) ∧
    (∀ a b c : ℤ, a ≠ 0 → a ∣ b → ∀ A : Set ℤ,
      ¬ ExactComplement A (fun x => a*x^2+b*x+c)) := by
  exact ⟨exists_sixth_power_complement,
    fun a b c ha hab A => no_divisible_quadratic_complement a b c ha hab A⟩

end JSP000388
