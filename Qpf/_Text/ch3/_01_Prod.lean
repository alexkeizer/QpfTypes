
import Qpf

namespace Qpf

namespace Prod

def A := Unit

def B : A → TypeVec 2
  := fun _ => ![Unit, Unit]

def P : MvPFunctor 2 := ⟨A, B⟩

abbrev QpfProd := P.Obj

/-!

-/
abbrev Prod' : TypeFun 2
  := @TypeFun.ofCurried 2 Prod


def box : Prod' Γ → QpfProd Γ
  | ⟨a, b⟩ => ⟨
      (), 
      fun 
      | 1, _ => a
      | 0, _ => b
  ⟩

def unbox : QpfProd Γ → Prod' Γ
  | ⟨_, f⟩ => (f 1 (), f 0 ())

theorem unbox_box_id (x : Prod' Γ) :
  unbox (box x) = x :=
by
  rfl

theorem box_unbox_id (x : QpfProd Γ) :
  box (unbox x) = x :=
by
  cases x;
  simp[box, unbox];
  apply congrArg;
  funext i;
  cases i;
  case fz   => rfl
  case fs i => 
    cases i
    . rfl
    . contradiction



instance : MvQpf Prod' where
  P           := P
  map f a     := unbox <| P.map f <| box a
  abs         := @unbox
  repr        := @box
  abs_repr    := unbox_box_id
  abs_map f x := rfl

  

end Prod



end Qpf