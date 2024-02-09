/-
  Provides an instance of `MvQPF` for (the uncurried version of) the `Sum` built-in type
-/

import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr
import Qpf.Util

namespace MvQPF
namespace Sum

universe u

def SumPFunctor : MvPFunctor.{u} 2
  := ⟨PFin2 2, 
      fun 
      | 0 => myvec[PFin2 1, PFin2 0] -- inl
      | 1 => myvec[PFin2 0, PFin2 1] -- inr
    ⟩


abbrev QpfSum' := SumPFunctor.Obj
abbrev QpfSum  := TypeFun.curried QpfSum'

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

def equiv {Γ} : Sum' Γ ≃ QpfSum' Γ :=
{
  toFun   := box
  invFun  := unbox
  left_inv  := by intro x; cases x <;> rfl
  right_inv := by 
    intro x
    rcases x with ⟨i, f⟩
    dsimp only [box, unbox, inl, inr];
    fin_destr i <;> {
      apply congrArg;
      fin_destr <;> rfl
    }
} 

instance : MvQPF.IsPolynomial Sum' := 
  .ofEquiv _ equiv



end Sum

export Sum (QpfSum QpfSum')

end MvQPF
