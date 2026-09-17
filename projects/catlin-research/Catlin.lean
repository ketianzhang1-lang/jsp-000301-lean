import Profile
import Subdivision
import Colouring

namespace CatlinComplete
open CatlinCertificates

/-- Every hypothetical K8 subdivision requires more internal vertices
    than the seven vertices outside its branch set. -/
theorem no_K8_subdivision : ¬ContainsCliqueSubdivision 8 := by
  rintro ⟨B, hB, ⟨S⟩⟩
  have hlow := budget_ge_eight B hB
  have hupp := subdivision_budget_bound S
  omega

/-- The complete known Catlin counterexample, with genuine graph paths.
    This does not prove the asymptotic statement of JSP-000585. -/
theorem catlin_counterexample :
    graph.chromaticNumber = 8 ∧ ¬ContainsCliqueSubdivision 8 :=
  ⟨chromaticNumber_eq_eight, no_K8_subdivision⟩

end CatlinComplete
