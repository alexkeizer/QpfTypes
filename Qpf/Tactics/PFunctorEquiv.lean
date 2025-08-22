import Mathlib.Data.PFunctor.Multivariate.Basic
import Qq

import Qpf.Util
import Qpf.Elab.TraceClass

/-!
# `pfunctor_equiv` tactic
-/

open MvFunctor in
abbrev MvPFunctor.Obj.mk.{u} {P : MvPFunctor.{u} n} {αs : TypeVec n}
    (a : P.A) (f : P.B a ⟹ αs) : P.Obj αs :=
  ⟨a, f⟩

namespace QpfTypes.Tactics
open Lean Meta Elab.Tactic
open Qq

elab "intro_vec" : tactic => withMainContext <| do
  let goal ← getMainGoal
  let ⟨αs, goal⟩ ← goal.intro (← Core.mkFreshUserName `αs)
  let n ← mkFreshExprMVarQ q(Nat)
  let u ← mkFreshLevelMVar
  let αsType ← αs.getType
  let expected := q(TypeVec.{u} $n)
  unless ← isDefEq αsType expected do
    throwError "Binder {← mkHasTypeButIsExpectedMsg αsType expected}"

  -- let newGoal ← mkFreshExprMVar (userName := ← goal.getTag) _

  return ()

namespace PFunctorEquiv

-- def typevecTelescope

/--
Return an expression `box` of type `F α₁ … αₙ → P !![α₁, …, αₙ]`.

That is, `box` maps objects from the curried form, to the internal uncurried form.

For example, using a simple list type
```lean4
  fun x => match x with
| MyList.Shape.nil a b => ⟨MyList.Shape.HeadT.nil, fun i => match i with
    | 0 => Fin2.elim0 (C:=fun _ => _)
    | 1 => fun j => match j with
            | (.ofNat' 0) => b
    | 2 => fun j => match j with
            | (.ofNat' 0) => a
⟩
| MyList.Shape.cons a as => ⟨MyList.Shape.HeadT.cons, fun i j => match i with
    | 0 => match j with
            | .fz => as
    | 1 => Fin2.elim0 (C:=fun _ => _) j
    | 2 => match j with
            | .fz => a
```
-/
def deriveBox {u : Level} (F P : Q(Type u)) (Pinfo : Expr) : MetaM Expr := do
  let (Fn, Fparams) := F.withApp (·, ·)
  unless Fn.isConst do
    throwError "Expected an application of an inductive type, but found:\n\t{F}"
  let Finfo ← getConstInfoInduct Fn.constName
  let ctors ← Finfo.ctors.mapM getConstInfoCtor

  let numCtors : Nat := ctors.length
  unless Finfo.numIndices = 0 do
    throwError "Inductive families are not supported; `{Fn}` has {Finfo.numIndices} indices"

  trace[QPFTypes] "F: {Fn}"
  trace[QPFTypes] "Fparams: {Fparams}"

  withLocalDeclD `x F fun x => do
    let casesOn := Expr.const (Fn.constName.str "casesOn") (Fn.constLevels! ++ [u.succ])
    let motive := Expr.lam .anonymous (← mkFreshExprMVar none) P .default
    let casesOn := mkAppN casesOn (Fparams ++ #[motive, x])
    let casesOn :=
      mkAppN casesOn <| List.toArray <|← ctors.mapM fun ctor => do
        let ctorType :=
          ctor.type.getForallBodyMaxDepth Finfo.numParams
          |>.instantiate Fparams
        forallTelescopeReducing ctorType fun ctorArgs ctorType => do
          trace[QPFTypes] "ctor `{ctor.name}` has type:\n\t{ctor.type}\
            \nand arguments:\n\t{ctorArgs}\
            \nwith residual:\n\t{ctorType}"

          let a ← mkAppOptM ``OfNat.ofNat #[
              q(Fin $numCtors), (toExpr ctor.cidx), none
            ]
          let f ← mkFreshExprMVar none
          let obj ← mkAppOptM ``MvPFunctor.Obj.mk #[
              none, Pinfo, none, a, f
            ]
          mkLambdaFVars ctorArgs obj
    mkLambdaFVars #[x] casesOn

#check MvPFunctor.Obj

/--
Closes a main goal of type: `∀ (αs : TypeVec $n), ($P).Obj αs = (TypeFun.ofCurried $F) αs`
-/
def solveEquiv {u : Level} {n : Q(Nat)} (P : Q(MvPFunctor.{u} $n))
    (F : Q(CurriedTypeFun.{u, u} $n)) : TacticM Unit := do
  return ()

def elabPFunctorEquiv : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let n ← mkFreshExprMVarQ q(Nat)
  let u ← mkFreshLevelMVar
  let P ← mkFreshExprMVarQ q(MvPFunctor.{u} $n)
  let F ← mkFreshExprMVarQ q(CurriedTypeFun.{u, u} $n)

  let expectedTarget := q(∀ (αs : TypeVec $n), ($P).Obj αs = (TypeFun.ofCurried $F) αs)
  if (← isDefEq target expectedTarget) then
    solveEquiv (u:=u) (n:=n) P F
  else
    throwError "Failed to unify goal:\n\t{target}\n with the expected target:\n\t{expectedTarget}"

  return ()

end PFunctorEquiv

scoped elab "pfunctor_equiv" : tactic => PFunctorEquiv.elabPFunctorEquiv

/-! ## Tests -/
namespace Test

def SumP : MvPFunctor 2 where
  A := Fin 2
  B := List.get [
          !![Fin 0, Fin 1],
          !![Fin 1, Fin 0]
        ]

def ProdP : MvPFunctor 2 where
  A := Fin 1
  B := List.get [
        !![Fin 1, Fin 1]
       ]

def ProdP.mk (x : α) (y : β) : ProdP.Obj !![β, α] :=
  ⟨(0 : Fin 1), fun
      | 0, _ => x
      | 1, _ => y
    ⟩

set_option trace.QPFTypes true
#eval do
  let α ← mkFreshExprMVarQ q(Type)
  let β ← mkFreshExprMVarQ q(Type)
  @PFunctorEquiv.deriveBox 0 q(Prod $α $β) q(ProdP.Obj !![$α, $β]) q(ProdP)

example : ∀ αs, SumP αs ≃ (TypeFun.ofCurried Sum) αs := by
  intro αs
  suffices ∀ (α β : Type),
    SumP !![α, β] ≃ Sum α β
  by
    sorry
    -- simpa using this (αs 0) (αs 1)
  intro α β

  unfold MvPFunctor.Obj
  apply Equiv.mk
  sorry
