import Lake
open Lake DSL
package JSP000476 where
  version := v!"0.3.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"
lean_lib ErdosProblems
lean_lib HasseWeil
lean_lib Waring
lean_lib UnitFractions
@[default_target]
lean_lib JSP000476 where
  roots := #[`JSP000476, `JSP000476Complete]
