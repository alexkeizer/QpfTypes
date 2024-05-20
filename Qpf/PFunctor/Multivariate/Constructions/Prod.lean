/-
  Provides an instance of `MvQPF` for (the uncurried version of) the `Prod` built-in type
-/

import Mathlib.Data.QPF.Multivariate.Basic
import Mathlib.Tactic.FinCases

import Qpf.Util
import Qpf.Macro.Tactic.FinDestr
import Qpf.Qpf.Multivariate.Basic

namespace MvQPF
namespace Prod

open PFin2 (fz fs)

def P : MvPFunctor 2
  := .mk Unit fun _ _ => PFin2 1


abbrev QpfProd' := P.Obj
abbrev QpfProd  := TypeFun.curried QpfProd'

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

def equiv {Γ} : Prod' Γ ≃ QpfProd' Γ := {
  toFun     := fun ⟨a, b⟩ => mk a b,
  invFun    := fun ⟨_, f⟩ => (f 1 fz, f 0 fz),
  left_inv  := by intro _; rfl,
  right_inv := by
    intro x;
    rcases x with ⟨⟨⟩, f⟩;
    simp[mk];
    apply congrArg;
    funext i (j : PFin2 _)
    fin_cases j
    fin_cases i
    <;> rfl
}

instance : MvFunctor Prod' where
  map f x   := equiv.invFun <| P.map f <| equiv.toFun <| x

instance : MvQPF.IsPolynomial Prod' := .ofEquiv _ equiv


end Prod

export Prod (QpfProd QpfProd')

end MvQPF
