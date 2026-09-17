import Lake
open Lake DSL

package Catlin where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib Catlin where
  roots := #[`Certificate, `GraphCore, `Profile, `Subdivision, `Colouring, `Catlin, `Sharp]
