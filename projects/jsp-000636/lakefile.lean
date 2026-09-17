import Lake
open Lake DSL
package JSP000636 where
  version := v!"0.1.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
@[default_target]
lean_lib JSP000636 where
  roots := #[`JSP000636, `Lower, `Upper, `Construction, `Threshold, `Thinning]
