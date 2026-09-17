import Lake
open Lake DSL

-- Keep the package and root module names identical because lean-action's
-- NaNoda integration extracts the package name from this declaration.
package JSP000399 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib JSP000399 where
  roots := #[`JSP000399, `Compatibility]
