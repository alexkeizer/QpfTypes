import Lake
open Lake DSL

package qpf {
}

@[default_target]
lean_lib Qpf

lean_lib Test

require mathlib from git
  "https://github.com/monsterkrampe/mathlib4.git"@"PFunctor-universe-refactoring"
