import Qpf.Qpf.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr

namespace MvQpf
namespace Prod

def ProdPFunctor : MvPFunctor 2 
  := ⟨PUnit, fun _ => ![PFin2 1, PFin2 1]⟩

abbrev QpfProd' := ProdPFunctor.Obj
abbrev QpfProd  := QpfProd'.curried

/--
  An uncurried version of the root `Prod`
-/
abbrev Prod' : TypeFun 2
  := @TypeFun.ofCurried 2 Prod


/--
  Constructor for `QpfProd'`
-/
def mk (a : Γ 1) (b : Γ 0) : QpfProd' Γ
  := ⟨
      (), 
      fun 
      | 1, _ => a
      | 0, _ => b
  ⟩


def box : Prod' Γ → QpfProd' Γ
  | ⟨a, b⟩ => mk a b

def unbox : QpfProd' Γ → Prod' Γ
  | ⟨_, f⟩ => (f 1 .fz, f 0 .fz)

theorem unbox_box_id (x : Prod' Γ) :
  unbox (box x) = x :=
by
  rfl

theorem box_unbox_id (x : QpfProd' Γ) :
  box (unbox x) = x :=
by
  cases x;
  simp[box, unbox, mk];
  apply congrArg;
  fin_destr
  <;> rfl



instance : MvQpf Prod' where
  P           := ProdPFunctor
  map f a     := unbox <| ProdPFunctor.map f <| box a
  abs         := @unbox
  repr        := @box
  abs_repr    := unbox_box_id
  abs_map f x := rfl

  

end Prod

export Prod (QpfProd QpfProd')

end MvQpf