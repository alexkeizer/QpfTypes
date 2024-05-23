import Qpf

universe u v w

/-- info: MvQPF.Arrow ?α : CurriedTypeFun 1 -/
#guard_msgs in
  #check MvQPF.Arrow ?α

data Arrow (α : Type) β : Type u
  | mk : (α → β) → Arrow α β

/-- info: Arrow : Type → CurriedTypeFun 1 -/
#guard_msgs in
  #check (Arrow : Type → Type → Type)

/-- info: Arrow.Shape : Type u → Type v → Type w → Type w -/
#guard_msgs in #check (Arrow.Shape : Type u → Type v → Type w → Type w)

/-- info: Arrow.Base : Type → TypeFun 2 -/
#guard_msgs in #check (Arrow.Base : Type → TypeFun.{u, u} 2)

#synth MvQPF (Arrow.Base _ : TypeFun.{0} 2)
-- ^^^ We know that the `Base` is a QPF for universe 0

#synth MvQPF (Arrow.Base _ : TypeFun.{1} 2)
-- ^^^ But, somehow we can't synthesize this fact for higher universes

#check (Arrow.Uncurried : Type → TypeFun.{1} 1)
-- ^^^ Which, presumably, is why `Uncurried` is *not* polymorphic



/-- info: Arrow : Type → CurriedTypeFun 1 -/
#guard_msgs in
  #check (Arrow : Type → Type u → Type u)
