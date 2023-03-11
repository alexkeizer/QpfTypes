import Lake
open Lake DSL

package qpf {
}

@[default_target]
lean_lib Qpf

require mathlib from git "https://github.com/alexkeizer/mathlib4.git" @ "alexkeizer/isPolynomial"
