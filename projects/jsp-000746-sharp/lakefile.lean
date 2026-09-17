import Lake
open Lake DSL

package JSP000746 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib JSP000746 where
  roots := #[`Erdos895, `JSP000746Sharp, `JSP000746]
