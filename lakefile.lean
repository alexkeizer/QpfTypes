import Lake
open Lake DSL

package qpf {
  -- add configuration options here
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "800bc41ecd44473c28473f9d2e83919aead32b2d"
  }]
}
