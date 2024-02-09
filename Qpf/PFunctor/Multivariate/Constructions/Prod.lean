/-
  Provides an instance of `MvQPF` for (the uncurried version of) the `Prod` built-in type
-/

import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util
import Qpf.Macro.Tactic.FinDestr

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

instance : MvQPF.IsPolynomial Prod' := .ofEquiv _
{
  toFun     := fun ⟨a, b⟩ => mk a b,
  invFun    := fun ⟨_, f⟩ => (f 1 fz, f 0 fz),
  left_inv  := by intro _; rfl,
  right_inv := by
    intro x;
    rcases x with ⟨⟨⟩, f⟩;
    simp[mk];
    apply congrArg;
    funext i j
    fin_destr i j;
    rfl
}

  

end Prod

export Prod (QpfProd QpfProd')

end MvQPF
