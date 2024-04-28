import Qpf


/-
  # Dead variables
-/


codata FinAlt {n : Nat} β
  | mk : Fin2 n → FinAlt β

#print FinAlt.mk


data QpfList₄ (dead : Type) β γ where
  | nil   : QpfList₄ dead β γ
  | cons  : QpfList₄ dead β γ → QpfList₄ dead β γ
