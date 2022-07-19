
import Qpf.Qpf.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr

namespace MvQpf 

namespace Arrow 

  def ArrowPFunctor (x : Type u) : MvPFunctor.{u} 1
    := ⟨PUnit, fun _ => ![x]⟩

  def QpfArrow' (x : Type _) : TypeFun 1
    := (ArrowPFunctor x).Obj

  /--
    A constructor for arrow types `x → y`, which is functorial in `y`
  -/
  abbrev QpfArrow : CurriedTypeFun 2
    := fun x => (QpfArrow' x).curried


  instance : MvQpf (QpfArrow' x) :=
    by unfold QpfArrow'; infer_instance

  abbrev Arrow (x : Type u) : CurriedTypeFun 1
    := (x → ·)

  abbrev Arrow' (x : Type u) : TypeFun 1
    := TypeFun.ofCurried (Arrow x)


  theorem Arrow.eta {α β : Type u} :
    (α → β) = Arrow α β :=
  rfl


  
  def box (f : Arrow' α Γ) : (QpfArrow' α Γ)
    := ⟨(), fun | 0 => f⟩

  def unbox : QpfArrow' α Γ → Arrow' α Γ
    | ⟨_, f⟩ => f 0

  theorem box_unbox_id (f : QpfArrow' α Γ) :
    box (unbox f) = f :=
  by
    simp[box, unbox]
    apply congrArg;
    fin_destr;
    rfl
      

  theorem unbox_box_id (f : Arrow' α Γ) :
    unbox (box f) = f :=
  by
    rfl



  instance : MvQpf (Arrow' x) where
    P           := ArrowPFunctor x
    map f a     := unbox <| (ArrowPFunctor x).map f <| box a
    abs         := @unbox x
    repr        := @box x
    abs_repr    := unbox_box_id
    abs_map f x := rfl

end Arrow

export Arrow (QpfArrow QpfArrow' Arrow Arrow')

end MvQpf