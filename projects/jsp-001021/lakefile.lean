import Lake
open Lake DSL

package JSP001021 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib JSP001021 where
  roots := #[`ErdosProblems.Erdos1216.Certificates, `ErdosProblems.Erdos1216, `FiniteChecks, `JSP001021]
