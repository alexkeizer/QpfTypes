import Qpf.Qpf.Multivariate.Basic
import Qpf.Qpf.Multivariate.ofPolynomial
import Qpf.PFunctor.Multivariate.Constructions.Basic
import Qpf.Macro.Tactic.FinDestr

namespace MvQpf
namespace Prod

open PFin2 (fz fs)

def P : MvPFunctor 2 
  := .mk' [
    ![1, 1]
  ]



def P' : MvPFunctor 2 
  := ⟨PFin2 1, 
      fun | _ => ![PFin2 1, PFin2 1]
   ⟩


def Pfin : MvPFunctor 2 
    := ⟨Fin 1, 
        fun | _ => ![Fin 1, Fin 1]
    ⟩

 


-- `Nat` lives in `Type`, so both functors are fine 
#check (P.Obj ![Nat, Nat] : Type)
#check (Pfin.Obj ![Nat, Nat] : Type)

-- Now assume some `X` that lives in a higher universe, say `Type 1`
variable (X : Type 1)

-- `P` is able to adjust 
#check (P.Obj ![X, X] : Type 1)

-- `Pfin` is not
-- #check Pfin.Obj ![X, X]
-- application type mismatch
--   Vec.append1 Vec.nil X
-- argument
--   X
-- has type
--   Type 1 : Type 2
-- but is expected to have type
--   Type : Type 1


-- #check P.Obj ![Nat, X]

abbrev QpfProd' := P.Obj
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
      fz, 
      fun 
      | 1, _ => a
      | 0, _ => b
  ⟩


def box : Prod' Γ → QpfProd' Γ
  | ⟨a, b⟩ => mk a b

def unbox : QpfProd' Γ → Prod' Γ
  | ⟨fz, f⟩ => (f 1 fz, f 0 fz)

theorem unbox_box_id (x : Prod' Γ) :
  unbox (box x) = x :=
by
  rfl

theorem box_unbox_id (x : QpfProd' Γ) :
  box (unbox x) = x :=
by
  rcases x with ⟨i, f⟩;
  fin_destr i;
  simp[box, unbox, mk];
  apply congrArg;
  fin_destr
  <;> rfl



instance : MvQpf Prod' := .ofPolynomial P box unbox box_unbox_id

  

end Prod

export Prod (QpfProd QpfProd')

end MvQpf