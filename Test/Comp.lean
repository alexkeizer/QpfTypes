import Qpf
-- import Test.List

-- open Test


/-
  # Composition pipeline
-/

set_option trace.QPF true
qpf P₁ α β := α
#check P₁
#check P₁.Uncurried

#exit

qpf P₂ α β := β

qpf C₁ α β := Nat
qpf C₂ (n : Nat) α β := PFin2 n

qpf G₄ α β ρ := QpfList ρ
