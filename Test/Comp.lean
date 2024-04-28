import Qpf
import Test.List

open Test


/-
  # Composition pipeline
-/

qpf P₁ α β := α
qpf P₂ α β := β

qpf C₁ α β := Nat
qpf C₂ (n : Nat) α β := Fin2 n

qpf G₄ α β ρ := QpfList ρ
