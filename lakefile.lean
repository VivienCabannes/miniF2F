import Lake
open Lake DSL

package «minif2f»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «MiniF2F»
