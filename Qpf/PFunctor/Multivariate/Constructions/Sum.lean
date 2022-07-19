import Qpf.Qpf.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr

namespace MvQpf
namespace Sum

universe u

def SumPFunctor : MvPFunctor.{u} 2
  := ⟨PFin2 2, 
      fun 
      | 0 => ![PFin2 1, PFin2 0] -- inl
      | 1 => ![PFin2 0, PFin2 1] -- inr
    ⟩


abbrev QpfSum' := SumPFunctor.Obj
abbrev QpfSum  := QpfSum'.curried

def inl {Γ : TypeVec 2} (a : Γ 1) : QpfSum' Γ
  := ⟨PFin2.ofNat' 0, 
      fun 
      | 1, _ => a
    ⟩

def inr {Γ : TypeVec 2} (b : Γ 0) : QpfSum' Γ
  := ⟨PFin2.ofNat' 1, 
      fun 
      | 0, _ => b
      | 1, x => by cases x
    ⟩


abbrev Sum' := @TypeFun.ofCurried 2 Sum

def box {Γ : TypeVec 2} : Sum' Γ → QpfSum' Γ
  | .inl a => inl a
  | .inr b => inr b

def unbox {Γ : TypeVec 2} : QpfSum' Γ → Sum' Γ 
  | ⟨i, f⟩ => match i with
    | .fz   => .inl (f 1 .fz)
    | .fs 0 => .inr (f 0 .fz)


theorem unbox_box_id (x : Sum' Γ) :
  unbox (box x) = x :=
by
  cases x <;> rfl

theorem box_unbox_id (x : QpfSum' Γ) :
  box (unbox x) = x :=
by
  rcases x with ⟨i, f⟩
  dsimp only [box, unbox, inl, inr];
  fin_destr i <;> {
    apply congrArg;
    fin_destr <;> rfl
  }


instance : MvQpf Sum' where
  P           := SumPFunctor
  map f a     := unbox <| SumPFunctor.map f <| box a
  abs         := @unbox
  repr        := @box
  abs_repr    := unbox_box_id
  abs_map f x := by 
                  rcases x with ⟨i, f⟩ 
                  fin_destr i <;> rfl



end Sum

export Sum (QpfSum QpfSum')

end MvQpf