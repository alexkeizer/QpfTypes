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

import Qq

namespace Macro.Comp
open MvQPF
open Lean Elab Term Command Meta
open PrettyPrinter (delab)
open Syntax
-- open Parser (ident)
open Parser.Term (bracketedBinder)
open Parser.Command (declModifiers «def»)

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
protected def parseApp (isLiveVar : FVarId → Bool) (F : Q(Type u)) :
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


def Fin2.toExpr {n : Nat} : Fin2 n → Q(Fin2 $n)
  | .fz   => q(Fin2.fz)
  | .fs i => q(Fin2.fs $(toExpr i))

instance {n : Nat} : ToExpr (Fin2 n) where
  toExpr      := Fin2.toExpr
  toTypeExpr  := q(Fin2 $n)


def Vec.toExpr {α : Q(Type u)} : {n : Nat} → Vec Q($α) n → Q(Vec $α $n)
  | 0,   _  => q(Vec.nil)
  | _+1, as =>
    let a : Q($α) := as.last
    let as := toExpr as.drop
    q(Vec.append1 $as $a)

instance {α : Q(Type u)} {n : Nat} : ToExpr (Vec Q($α) n) where
  toExpr      := Vec.toExpr
  toTypeExpr  := q(Vec $α $n)

def DVec.toExpr {n : Nat} {αs : Q(Fin2 $n → Type u)} (xs : DVec (fun (i : Fin2 n) => Q($αs $i))) :
    Q(DVec.{u} $αs) :=
  match n with
  | 0   => q(Fin2.elim0)
  | _+1 =>
    let a : Q($αs 0) := xs.last
    let as := toExpr xs.drop
    q(fun
      | .fz   => $a
      | .fs i => $as i
    )


structure ElabQpfResult (u : Level) (arity : Nat) where
  F : Q(TypeFun.{u,u} $arity)
  functor : Q(MvFunctor $F)
  qpf     : Q(@MvQPF _ $F $functor)
deriving Inhabited

open PrettyPrinter in
mutual
partial def handleLiveFVar (vars : Vector Q(Type u) arity) (target : Q(Type u))  : TermElabM (ElabQpfResult u arity) := do
  let vars' := vars.toList;

  trace[QPF] f!"target {target} is a free variable"
  let ind ← match List.indexOf' target vars' with
  | none      => throwError "Free variable {target} is not one of the qpf arguments"
  | some ind  => pure ind

  let ind : Fin2 arity := cast (by simp [vars']) ind.inv
  let prj := q(@Prj.{u} $arity $ind)
  trace[QPF] "represented by: {prj}"
  pure ⟨prj, q(Prj.mvfunctor _), q(Prj.mvqpf _)⟩

partial def handleConst (vars : Vector Q(Type u) arity) (target : Q(Type u))  : TermElabM (ElabQpfResult u arity) := do
  trace[QPF] "target {target} is a constant"
  let const := q(Const.{u} $arity $target)
  trace[QPF] "represented by: {const}"
  pure ⟨const, q(Const.MvFunctor), q(Const.mvqpf)⟩

partial def handleApp (vars : Vector Q(Type u) arity) (target : Q(Type u))  : TermElabM (ElabQpfResult u arity) := do
  let vars' := vars.toList;

  let varIds := vars'.map fun expr => expr.fvarId!
  let isLiveVar : FVarId → Bool
    := fun fvarId => (List.indexOf' fvarId varIds).isSome

  let ⟨m, F, args⟩ ← (Comp.parseApp isLiveVar target)
  trace[QPF] "target {target} is an application of {F} to {args.toList}"

  /-
    Optimization: check if the application is of the form `F α β γ .. = F α β γ ..`.
    In such cases, we can directly return `F`, rather than generate a composition of projections.
  -/
  let is_trivial :=
    args.length == arity
    && args.toList.enum.all fun ⟨i, arg⟩ =>
        arg.isFVar && isLiveVar arg.fvarId! && vars'.indexOf arg == i
  if is_trivial then
    trace[QPF] "The application is trivial"
    let mvFunctor ← synthInstanceQ q(MvFunctor $F)
    let mvQPF ← synthInstanceQ q(MvQPF $F)
    pure ⟨F, mvFunctor, mvQPF⟩
  else
    let G ← args.toList.mapM fun a =>
      elabQpf vars a none false

    /-
      HACK: We know that `m`, which was defines as `args.length`, is equal to `G.length`.
      It's a bit difficult to prove this. Thus, we simply assert it
    -/
    if hm : m ≠ G.length then
      throwError "This shouldn't happen" -- TODO: come up with a better error message
    else
      have hm : m = G.length := by simpa using hm



      let Ffunctor ← synthInstanceQ q(MvFunctor $F)
      let Fqpf ← synthInstanceQ q(@MvQPF _ $F $Ffunctor)

      let G : Vec _ m := fun i => G.get (hm ▸ i.inv)
      let GExpr : Q(Vec (TypeFun.{u,u} $arity) $m) :=
        Vec.toExpr (fun i => (G i).F)
      let GFunctor : Q(∀ i, MvFunctor.{u,u} ($GExpr i)) :=
        let αs := q(fun i => MvFunctor.{u,u} ($GExpr i))
        @DVec.toExpr _ _ αs (fun i => (G i).functor)
      let GQpf : Q(∀ i, @MvQPF.{u,u} _ _ ($GFunctor i)) :=
        let αs := q(fun i => @MvQPF.{u,u} _ _ ($GFunctor i))
        @DVec.toExpr _ _ αs (fun i => (G i).qpf)

      let comp := q(@Comp $m _ $F $GExpr)
      trace[QPF] "G := {GExpr}"
      trace[QPF] "comp := {comp}"

      let functor := q(Comp.instMvFunctorComp)
      let qpf := q(Comp.instMvQPFCompInstMvFunctorCompFin2
        (fF := $Ffunctor) (q := $Fqpf) (fG := _) (q' := $GQpf)
      )
      pure ⟨comp, functor, qpf⟩


partial def handleArrow (vars : Vector Q(Type u) arity) (target : Q(Type u)) (targetStx : Option Term := none) (normalized := false) : TermElabM (ElabQpfResult u arity) := do
  match target with
  | Expr.forallE _ e₁ e₂ .. =>
    let newTarget ← mkAppM ``MvQPF.Arrow.Arrow #[e₁, e₂]
    elabQpf vars newTarget targetStx normalized
  | _ => unreachable!

/--
  Elaborate the body of a qpf
-/
partial def elabQpf {arity : Nat} (vars : Vector Q(Type u) arity) (target : Q(Type u)) (targetStx : Option Term := none) (normalized := false) :
    TermElabM (ElabQpfResult u arity) := do
  trace[QPF] "elabQPF :: {vars.toList} -> {target}"
  let vars' := vars.toList;

  let varIds := vars'.map fun expr => expr.fvarId!
  let isLiveVar : FVarId → Bool
    := fun fvarId => (List.indexOf' fvarId varIds).isSome

  if target.isFVar && isLiveVar target.fvarId! then
    handleLiveFVar vars target
  else if !target.hasAnyFVar isLiveVar then
    handleConst vars target
  else if target.isApp then
    handleApp vars target
  else if target.isArrow then
    handleArrow vars target (targetStx := targetStx) (normalized := normalized)
  else
    if !normalized then
      let target ← whnfR target
      elabQpf vars target targetStx true
    else
      let extra :=
        if target.isForall then
          "Dependent arrows / forall are not supported"
        else
          ""
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
      CommandElabM (Term × Term × Term) := do
  trace[QPF] "elabQpfCompositionBody ::
    type?       := {view.type?}
    target      := {view.target}
    liveBinders := {view.liveBinders}
    deadBinders := {view.deadBinders}
  "
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
            let res ← elabQpf vars target_expr view.target

            res.F.check
            res.functor.check
            res.qpf.check

            withOptions (fun opt => opt.insert `pp.explicit true) <| do
              let F ← delab res.F
              let functor ← delab res.functor
              let qpf ← delab res.qpf
              return ⟨F, functor, qpf⟩


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
  let ⟨body, functor, qpf⟩ ← elabQpfCompositionBody {
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
      instance : MvFunctor ($F_internal_applied) := $functor:term

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
