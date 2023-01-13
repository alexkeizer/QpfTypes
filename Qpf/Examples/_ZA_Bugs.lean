import Qpf

/-!
  This file is a collection of examples that *should* compile, but currently don't
-/

/- Works when `α : Type`, but fails for higher universes -/
data HigherUniv (α : Type 2) β
  | mk : (α → β) → β → HigherUniv α β

/- Fails when β is repeated after a constant -/
data RepAfterConst β
  | mk : Nat → β → β → RepAfterConst β





-- qpf F α β γ := α

-- instance (F : CurriedTypeFun (n + 2)) (α : Type _) [q : MvQpf (TypeFun.ofCurried F)] : 
--     MvQpf (TypeFun.ofCurried (F α)) := 
-- by
  

-- #check (inferInstance : MvQpf <| TypeFun.ofCurried (F Nat))