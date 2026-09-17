import Lake
open Lake DSL

package JSP000393 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib JSP000393 where
  roots := #[`JSP000393]

lean_lib ErdosProblems where
  roots := #[`ErdosProblems.Erdos485]

@[default_target]
lean_lib JSP000393Complete where
  roots := #[`JSP000393Complete, `AuditComplete]
