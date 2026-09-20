import JSP000388Complete

/- Audit-owned specification, stated independently using the literal
value-pair formulation of Erdős 477. This is not submitted proof source. -/
namespace Verify388

def Tiles (A B : Set ℤ) : Prop :=
  ∀ z : ℤ, ∃! p ∈ A ×ˢ B, z = p.1 + p.2

theorem tiles_iff (A : Set ℤ) (f : ℤ → ℤ) :
    Tiles A (Set.range f) ↔ JSP000388.ExactComplement A f := by
  simp only [Tiles, JSP000388.ExactComplement, Set.mem_prod, and_assoc, eq_comm]

theorem original :
    ∃ f : Polynomial ℤ, 2 ≤ f.degree ∧
      ∃ A : Set ℤ, Tiles A (Set.range f.eval) :=
  JSP000388.jsp_000388

theorem sixth_power :
    ∃ A : Set ℤ, Tiles A (Set.range (fun x : ℤ => x ^ 6)) := by
  obtain ⟨A, hA⟩ := JSP000388.exists_sixth_power_complement
  exact ⟨A, (tiles_iff A _).mpr hA⟩

theorem every_integer_translate (c : ℤ) :
    ∃ A : Set ℤ,
      Tiles A (Set.range (fun x : ℤ =>
        (Polynomial.X ^ 6 + Polynomial.C c : Polynomial ℤ).eval x)) := by
  obtain ⟨A, hA⟩ := JSP000388.exists_shifted_polynomial_complement c
  exact ⟨A, (tiles_iff A _).mpr hA⟩

theorem quadratic_obstruction (a b c : ℤ) (ha : a ≠ 0) (hab : a ∣ b) :
    ∀ A : Set ℤ, ¬ Tiles A (Set.range (fun x : ℤ => a*x^2+b*x+c)) := by
  intro A hA
  exact JSP000388.no_divisible_quadratic_complement a b c ha hab A
    ((tiles_iff A _).mp hA)

end Verify388
