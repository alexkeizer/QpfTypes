import Qpf

/-!
  This file is a collection of examples that *should* compile, but currently don't
-/

/-
  Blocked on universe polymorphic `HeadT`!
-/
/- Works when `α : Type`, but fails for higher universes -/
data HigherUniv (α : Type 2) β
  | mk : (α → β) → β → HigherUniv α β

/- Fails when β is repeated after a constant -/
data RepAfterConst β
  | mk : Nat → β → β → RepAfterConst β





data QpfList₅ (A : Type) (dead : Type) β where
  | nil   : QpfList₅ A dead β
  | cons  : A → (dead → β) → QpfList₅ A dead β → QpfList₅ A dead β






/-
  Big issue for dead variables, it seems partial applications of QPFs don't automatically get
  an instance of MvQpf
-/


-- qpf F α β γ := α

-- instance (F : CurriedTypeFun (n + 2)) (α : Type _) [q : MvQpf (TypeFun.ofCurried F)] : 
--     MvQpf (TypeFun.ofCurried (F α)) := 
-- by
  

-- #check (inferInstance : MvQpf <| TypeFun.ofCurried (F Nat))