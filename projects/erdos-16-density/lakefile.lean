import Lake
open Lake DSL
package erdos16Density
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"
lean_lib Erdos16
lean_lib Erdos16Density
@[default_target] lean_lib Alignment
