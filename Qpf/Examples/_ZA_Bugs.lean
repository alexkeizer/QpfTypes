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



