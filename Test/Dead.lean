import Qpf


/-
  # Dead variables
-/


codata FinAlt {n : Nat} β
  | mk : PFin2 n → FinAlt β

/-- info: FinAlt.mk : PFin2 ?n → FinAlt ?β -/
#guard_msgs in #check @FinAlt.mk ?n ?β


data QpfList₄ (dead : Type) β γ where
  | nil   : QpfList₄ dead β γ
  | cons  : QpfList₄ dead β γ → QpfList₄ dead β γ
