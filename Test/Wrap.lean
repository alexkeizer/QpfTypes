import Qpf

universe u

namespace Test

data Wrap α
  | mk : α → Wrap α

/-- info: Test.Wrap.mk {α : Type} (a✝ : α) : Wrap α -/
#guard_msgs in
  #check Wrap.mk

/-- info: Wrap.Shape : Type u → Type u → Type u -/
#guard_msgs in
  #check (Wrap.Shape.{u} : CurriedTypeFun 2)

end Test
