import Lake
open Lake DSL

package qpf {
}

@[default_target]
lean_lib Qpf

lean_lib Test

require mathlib from "../mathlib4"
  -- git
  -- "https://github.com/leanprover-community/mathlib4.git"@"v4.7.0"
