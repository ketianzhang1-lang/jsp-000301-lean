import Lake
open Lake DSL
package JSP000506
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"
lean_lib Erdos625SelfContained
@[default_target]
lean_lib JSP000506 where
  roots := #[`JSP000506, `JSP000506Bridge, `JSP000506Complete]
