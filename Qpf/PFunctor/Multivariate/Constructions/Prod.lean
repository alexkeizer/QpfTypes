import Qpf.Qpf.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr

namespace MvQpf
namespace Prod

def ProdPFunctor : MvPFunctor 2 
  := ⟨PUnit, fun _ => ![PUnit, PUnit]⟩

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
  | ⟨_, f⟩ => (f 1 (), f 0 ())

theorem unbox_box_iso (x : Prod' Γ) :
  unbox (box x) = x :=
by
  rfl

theorem box_unbox_iso (x : QpfProd' Γ) :
  box (unbox x) = x :=
by
  cases x;
  simp[box, unbox, mk];
  apply congrArg;
  fin_destr



instance : MvQpf Prod' where
  P           := ProdPFunctor
  map f a     := unbox <| ProdPFunctor.map f <| box a
  abs         := @unbox
  repr        := @box
  abs_repr    := unbox_box_iso
  abs_map f x := rfl

  

end Prod

export Prod (QpfProd)

end MvQpf