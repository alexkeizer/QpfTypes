import Qpf.Qpf.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr

namespace MvQpf
namespace Sum

universe u

def SumPFunctor : MvPFunctor.{u} 2
  := ⟨PFin2 2, 
      fun 
      | 0 => ![PUnit, PEmpty] -- inl
      | 1 => ![PEmpty, PUnit] -- inr
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
      | 1, x => x.elim
    ⟩


abbrev Sum' := @TypeFun.ofCurried 2 Sum

def box {Γ : TypeVec 2} : Sum' Γ → QpfSum' Γ
  | .inl a => inl a
  | .inr b => inr b

def unbox {Γ : TypeVec 2} : QpfSum' Γ → Sum' Γ 
  | ⟨i, f⟩ => match i with
    | .fz   => .inl (f 1 ())
    | .fs 0 => .inr (f 0 ())


theorem unbox_box_iso (x : Sum' Γ) :
  unbox (box x) = x :=
by
  cases x <;> rfl

theorem box_unbox_iso (x : QpfSum' Γ) :
  box (unbox x) = x :=
by
  rcases x with ⟨i, f⟩
  simp[box, unbox]
  fin_destr i <;> {
    simp[inl, inr]
    apply congrArg;
    funext j x;
    fin_destr j
    <;> {
      try cases x
      try rfl
    }
  }


instance : MvQpf Sum' where
  P           := SumPFunctor
  map f a     := unbox <| SumPFunctor.map f <| box a
  abs         := @unbox
  repr        := @box
  abs_repr    := unbox_box_iso
  abs_map f x := by 
                  rcases x with ⟨i, f⟩ 
                  fin_destr i <;> rfl



end Sum
end MvQpf