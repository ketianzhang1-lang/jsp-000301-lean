import Lake
open Lake DSL
package JSP000465 where
  version := v!"0.1.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
@[default_target]
lean_lib JSP000465 where
  roots := #[`JSP000465]

lean_lib ErdosProblems where
  roots := #[
    `ErdosProblems.Erdos180.Foundations,
    `ErdosProblems.Erdos180.Geometry,
    `ErdosProblems.Erdos180.Subgraphs,
    `ErdosProblems.Erdos180.Counting,
    `ErdosProblems.Erdos180.Coordinates,
    `ErdosProblems.Erdos180.Counterexample,
    `ErdosProblems.Erdos180.Quantitative
  ]

