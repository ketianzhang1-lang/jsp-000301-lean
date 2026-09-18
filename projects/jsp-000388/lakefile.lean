import Lake
open Lake DSL
package JSP000388
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
@[default_target]
lean_lib JSP000388 where
  roots := #[`JSP000388, `JSP000388Complete, `AuditComplete]

lean_lib ErdosProblems where
  roots := #[`ErdosProblems.Erdos477]
