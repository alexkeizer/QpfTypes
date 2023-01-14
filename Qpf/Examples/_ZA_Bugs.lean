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



/-
  Big issue for dead variables, it seems partial applications of QPFs don't automatically get
  an instance of MvQpf
-/


-- qpf F α β γ := α

-- instance (F : CurriedTypeFun (n + 2)) (α : Type _) [q : MvQpf (TypeFun.ofCurried F)] : 
--     MvQpf (TypeFun.ofCurried (F α)) := 
-- by
  

-- #check (inferInstance : MvQpf <| TypeFun.ofCurried (F Nat))