import Lake
open Lake DSL

package «minif2f»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

lean_lib «test» where
  srcDir := "."

lean_lib «valid» where
  srcDir := "."

@[default_target]
lean_lib «MiniF2F»
