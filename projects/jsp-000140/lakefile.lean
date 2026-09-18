import Lake
open Lake DSL
package JSP000140
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
@[default_target]
lean_lib JSP000140 where
  roots := #[`JSP000140, `JSP000140Bridge, `JSP000140Complete, `AuditComplete]
lean_lib ErdosProblems where
  roots := #[`ErdosProblems.Erdos136]
