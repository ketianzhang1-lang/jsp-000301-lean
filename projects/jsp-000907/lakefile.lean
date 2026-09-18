import Lake
open Lake DSL
package JSP000907
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
@[default_target]
lean_lib JSP000907 where
  roots := #[`JSP000907Construction, `JSP000907OddRim, `JSP000907Witness,
    `JSP000907Complete, `AuditComplete]
lean_lib ErdosProblems where
  roots := #[`ErdosProblems.Erdos1091]
