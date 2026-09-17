import Lake
open Lake DSL

package JSP000399Triple where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib JSP000399Triple where
  roots := #[`Adapter, `JSP000399Triple]
