import Qpf

-- set_option trace.QPF true
-- set_option pp.raw true

namespace Test

data DeadWrap (α : Type) β
  | mk : α → DeadWrap α β

/-- info: 'Test.DeadWrap.Base' does not depend on any axioms  -/
#guard_msgs in
  #print axioms DeadWrap.Base

/-- info: Test.DeadWrap.mk {α β : Type} (a✝ : α) : DeadWrap α β -/
#guard_msgs in
  #check DeadWrap.mk

/-- info: DeadWrap.Shape.qpf -/
#guard_msgs in
  #synth MvQPF.IsPolynomial <| @TypeFun.ofCurried 3 DeadWrap.Shape

end Test
