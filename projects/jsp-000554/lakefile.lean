import Lake
open Lake DSL
package JSP000554
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
@[default_target]
lean_lib JSP000554 where
  roots := #[`JSP000554, `JSP000554Complete, `AuditComplete]
lean_lib ErdosProblems where
  roots := #[`ErdosProblems.Erdos682]
lean_lib PrimeNumberTheoremAnd where
  roots := #[`PrimeNumberTheoremAnd.Consequences]
lean_lib Util where
  roots := #[`Util.Density]
lean_lib UnitFractions where
  roots := #[`UnitFractions.ForMathlib.Misc]
