import Lake
open Lake DSL

package qpf {
}

@[default_target]
lean_lib Qpf

lean_lib Test

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.5.0"
