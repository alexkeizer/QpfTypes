/-
  This file establishes a `qpf` macro that can be used to define QPFs in an equational way.

  It supports simple projections, as in
  `qpf F₁ α β γ := γ`

  We can leave out the names for unused variables
  `qpf F₂ α _ _ := α`

  We can define constant functors, that don't depend on their variables at all
  `qpf F_int α β := Int`

  It's primary use is for (nested) compositions
  `qpf F₃ α β := F₁ β α (F_int β α)`


  Note that the macro just compiles these equations into the appropriate constructions on QPFs.
-/

import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Const
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.Vector.Basic

import Qpf.Qpf
import Qpf.Macro.Common
import Qpf.Macro.QpfExpr

import Qq

namespace Macro.Comp
open MvQPF
open Lean Elab Term Command Meta
open Mathlib (Vector)

open PrettyPrinter (delab)
open Syntax
open Parser.Term (bracketedBinder)
open Parser.Command (declModifiers definition)

open Macro (withQPFTraceNode)

open Qq

-- TODO: make everything work without this compatibility coercion
open TSyntax.Compat

def synthMvFunctor {n : Nat} (F : Q(TypeFun.{u,u} $n)) : MetaM Q(MvFunctor $F) := do
  let inst_type : Q(Type (u+1)) :=
    q(MvFunctor $F)
  synthInstanceQ inst_type

def synthQPF {n : Nat} (F : Q(TypeFun.{u,u} $n)) (_ : Q(MvFunctor $F)) : MetaM Q(MvQPF $F) := do
  let inst_type : Q(Type (u+1)) :=
    q(MvQPF $F)
  synthInstanceQ inst_type



/--
  Given an expression `e`, tries to find the largest subexpression `F` such that
    * `e = F α₀ ... αₙ`, for some list of arguments `α_i`, and
    * `F` contains no live variables, and
    * `F` is a QPF
  Then, tries to infer an instance of `MvQPF (TypeFun.curried F)`
-/
protected partial def parseApp (isLiveVar : FVarId → Bool) (F : Q(Type u)) :
    TermElabM ((n : Nat) × Q(TypeFun.{u,u} $n) × Vector Expr n) :=
  if F.isApp then
    /-
      HACK: Technically `F` is *not* an instance of `CurriedTypeFun 0`.
      However, we know that it is an application, and we only check the type after
      deconstructing the application
    -/
    parseAppAux F ⟨[], rfl⟩ none
  else
    throwError "application expected:\n {F}"

where
  parseAppAux : {n : Nat} → Q(CurriedTypeFun.{u,u} $n) → Vector Expr n → Option Exception → _
  | depth', Expr.app F a, args', _ => do
    let args := Vector.cons a args'
    let depth : Nat := depth' + 1
    let F : Q(CurriedTypeFun.{u,u} $depth) := F

    trace[QPF] "F := {F}\nargs := {args.toList}\ndepth := {depth}"
    F.check
    try
      -- Only try to infer QPF if `F` contains no live variables
      if !F.hasAnyFVar isLiveVar then
        let F : Q(TypeFun.{u,u} $depth)
          := q(TypeFun.ofCurried $F)
        let functor ← synthMvFunctor F
        let _ ← synthQPF F functor
        return ⟨depth, F, args⟩
      throwError "Smallest function subexpression still contains live variables:\n  {F}\ntry marking more variables as dead"
    catch e =>
      @parseAppAux depth F args (some e)

  | depth, F, args, e  => do
    if F.hasAnyFVar isLiveVar then
      match e with
      | some e => throw e
      | none =>
        throwError "Smallest function subexpression still contains live variables:\n  {F}\ntry marking more variables as dead"
    else
      trace[QPF] "F := {F}\nargs := {args.toList}\ndepth := {depth}"
      let F : Q(TypeFun.{u,u} $depth)
        := q(TypeFun.ofCurried $F)
      let functor ← synthMvFunctor F
      let _ ← synthQPF F functor
      return ⟨depth, F, args⟩

def List.indexOf' {α : Type} [BEq α] :  α → (as : List α) → Option (Fin2 (as.length))
  | _, []       =>  none
  | a, b :: bs  =>  if a == b then
                      some .fz
                    else
                      match indexOf' a bs with
                      | none   => none
                      | some i => some <| .fs i



-- structure QpfExpr (u : Level) (arity : Nat) where
--   F : Q(TypeFun.{u,u} $arity)
--   qpf     : Q(@MvQPF _ $F) := by exact q(by infer_instance)
-- deriving Inhabited

def isLiveVar (varIds : Vector FVarId n) (id : FVarId) := varIds.toList.contains id

open PrettyPrinter in
mutual
partial def handleLiveFVar (vars : Vector FVarId arity) (target : FVarId)  : TermElabM (QpfExpr u arity) := do
  trace[QPF] f!"target {Expr.fvar target} is a free variable"
  let ind ← match List.indexOf' target vars.toList with
  | none      => throwError "Free variable {Expr.fvar target} is not one of the qpf arguments"
  | some ind  => pure ind

  let ind : Fin2 arity := cast (by simp) ind.inv
  let prj := QpfExpr.prj ind
  trace[QPF] "represented by: {prj}"
  return prj

partial def handleConst (target : Q(Type u))  : TermElabM (QpfExpr u arity) := do
  trace[QPF] "target {target} is a constant"
  let const := QpfExpr.const _ target
  trace[QPF] "represented by: {const}"
  return const

partial def handleApp (vars : Vector FVarId arity) (target : Q(Type u)) : TermElabM (QpfExpr u arity) := do
  let vars' := vars.toList

  let ⟨numArgs, F, args⟩ ← (Comp.parseApp (isLiveVar vars) target)
  trace[QPF] "target {target} is an application of {F} to {args.toList}"
  let F ← QpfExpr.ofTypeFun F

  /-
    Optimization: check if the application is of the form `F α β γ .. = G α β γ ..`.
    In such cases, we can directly return `G`, rather than generate a composition of projections.
  -/
  let is_trivial := args.toList.mapM Expr.fvarId? == some vars'
  if is_trivial then
    trace[QPF] "The application is trivial"
    let some F := F.cast?
      | throwError "internal error: failed to cast {F} to be of arity {arity}"
    return F
  else
    let G ← args.mmap (elabQpf vars · none false)
    let G : Vec _ numArgs := fun i => G.get i.inv

    let C := QpfExpr.comp F G
    trace[QPF] "represented by: {C}"
    return C

partial def handleArrow (binderType body : Expr) (vars : Vector FVarId arity) (targetStx : Option Term := none) (normalized := false) : TermElabM (QpfExpr u arity) := do
  let newTarget ← mkAppM ``MvQPF.Arrow.Arrow #[binderType, body]
  elabQpf vars newTarget targetStx normalized

/--
  Elaborate the body of a qpf
-/
partial def elabQpf {arity : Nat} (vars : Vector FVarId arity) (target : Q(Type u)) (targetStx : Option Term := none) (normalized := false) :
    TermElabM (QpfExpr u arity) := do
  trace[QPF] "elabQPF :: {(vars.map Expr.fvar).toList} -> {target}"
  let isLiveVar := isLiveVar vars

  if let some target := target.fvarId?.filter isLiveVar then
    handleLiveFVar vars target
  else if !target.hasAnyFVar isLiveVar then
    handleConst target
  else if target.isApp then -- Could be pattern-matched here as well
    handleApp vars target
  else if let .forallE _ binderType body .. := target then
    handleArrow binderType body vars (normalized := normalized) (targetStx := targetStx)
  else if !normalized then
    let target ← whnfR target
    elabQpf vars target targetStx true
  else
    let extra := if target.isForall then "Dependent arrows / forall are not supported" else ""
    throwError f!"Unexpected target expression :\n {target}\n{extra}\nNote that the expression contains live variables, hence, must be functorial"
end

structure QpfCompositionBodyView where
  (type?  : Option Syntax := none)
  (target : Term)
  (liveBinders deadBinders : Array Syntax)



structure QpfCompositionBinders where
  (liveBinders deadBinders : Array Syntax)

/--
  Given the description of a QPF composition (`QpfCompositionView`), generate the syntax for a term
  that represents the desired functor (in uncurried form)
-/
def elabQpfCompositionBody (view: QpfCompositionBodyView) :
      CommandElabM (Term × Term) := do
  withQPFTraceNode "composition pipeline"
    (tag := "elabQpfCompositionBody") <| do

  withQPFTraceNode "arguments" <| do
    trace[QPF] "type?       := {view.type?}"
    trace[QPF] "target      := {view.target}"
    trace[QPF] "liveBinders := {view.liveBinders}"
    trace[QPF] "deadBinders := {view.deadBinders}"

  runTermElabM fun _ => do
    let u : Level ←
      if let some typeStx := view.type? then
        let type ← elabTerm typeStx (some <| .sort <|<- mkFreshLevelMVar)
        let type ← whnf type
        match type with
          | .sort (.succ u) => pure u
          | _ => throwErrorAt typeStx "invalid qpf, resulting type must be a type (e.g., `Type`, `Type _`, or `Type u`)"
      else
        mkFreshLevelMVar

    withAutoBoundImplicit <|
    elabBinders view.deadBinders fun _deadVars =>
    withLiveBinders view.liveBinders fun vars =>
    withoutAutoBoundImplicit <| do
      let target_expr ← elabTermEnsuringTypeQ (u:=u.succ.succ) view.target q(Type u)
      let arity := vars.toList.length
      let vars : Vector _ arity := ⟨vars.toList, rfl⟩

      let some vars := vars.mmap Expr.fvarId? |
        throwError "Expected all args to be fvars" -- TODO: throwErrorAt

      let res ← elabQpf vars target_expr view.target
      res.check

      withOptions (fun opt => opt.insert `pp.explicit true) <| do
        let F ← delab res.typeFun
        let qpf ← delab res.qpfInstance

        withQPFTraceNode "results …" <| do
          trace[QPF] "Functor := {F}"
          trace[QPF] "MvQPF instance := {qpf}"
        return ⟨F, qpf⟩


structure QpfCompositionView where
  (modifiers  : Modifiers := {})
  (F          : Name)                        -- Name of the functor to be defined
  (binders    : Syntax)
  (type?      : Option Term := none)
  (target     : Term)


/--
  Given the description of a QPF composition (`QpfCompositionView`), add a declaration for the
  desired functor (in both curried form as the `F` and uncurried form as `F.typefun`)
-/
def elabQpfComposition (view: QpfCompositionView) : CommandElabM Unit := do
  let (liveBinders, deadBinders) ← splitLiveAndDeadBinders view.binders.getArgs
  let (deadBindersNoHoles, deadBinderNames) ← mkFreshNamesForBinderHoles deadBinders


  /-
    Elaborate body
  -/
  let ⟨body, qpf⟩ ← elabQpfCompositionBody {
    type?   := view.type?
    target  := view.target
    liveBinders,
    deadBinders,
  }

  /-
    Define the qpf using the elaborated body
  -/
  let F_internal := mkIdent $ Name.mkStr view.F "Uncurried";
  let F := mkIdent view.F;
  let modifiers := quote (k := ``declModifiers) view.modifiers;

  let live_arity := mkNumLit liveBinders.size.repr;
  trace[QPF] "body: {body}"
  elabCommand <|← `(
      $modifiers:declModifiers
      def $F_internal:ident $deadBinders:bracketedBinder* :
        TypeFun $live_arity :=
      $body:term
  )

  let deadBinderNamedArgs ← deadBinderNames.mapM fun n => `(Parser.Term.namedArgument| ($n:ident := $n:term))
  let F_internal_applied ← `($F_internal $deadBinderNamedArgs:namedArgument*)


  let cmd ← `(
      $modifiers:declModifiers
      def $F:ident $deadBinders:bracketedBinder* : CurriedTypeFun $live_arity :=
        TypeFun.curried $F_internal_applied

      $modifiers:declModifiers
      instance $deadBinders:bracketedBinder* : MvQPF ($F_internal_applied) := $qpf:term
  )
  trace[QPF] "cmd: {cmd}"
  elabCommand cmd


  let F_applied ← `($F $deadBinderNamedArgs:namedArgument*)

  let cmd ← `(
    $modifiers:declModifiers
    instance : MvFunctor (TypeFun.ofCurried $F_applied) :=
      MvQPF.instMvFunctor_ofCurried_curried

    $modifiers:declModifiers
    instance $deadBindersNoHoles:bracketedBinder* : MvQPF (TypeFun.ofCurried $F_applied) :=
      MvQPF.instQPF_ofCurried_curried
  )
  trace[QPF] "cmd₂: {cmd}"
  elabCommand cmd



elab "qpf " F:ident sig:optDeclSig " := " target:term : command => do
  let type? := sig.raw[1]!
                  |>.getOptional?
                  |>.map fun sigInner =>
                            TSyntax.mk sigInner[1]!
  elabQpfComposition ⟨{}, F.getId, sig.raw[0]!, type?, target⟩




end Macro.Comp
