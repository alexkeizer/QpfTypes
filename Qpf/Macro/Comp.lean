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


def synthQPF {n : Nat} (F : Q(TypeFun.{u,u} $n)) : MetaM Q(MvQPF $F) := do
  let inst_type : Q(Type (u+1)) 
    := q(MvQPF $F)
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
    QQ.check F
    try
      -- Only try to infer QPF if `F` contains no live variables
      if !F.hasAnyFVar isLiveVar then        
        let F : Q(TypeFun.{u,u} $depth)
          := q(TypeFun.ofCurried $F)
        let _ ← synthQPF F
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
      let _ ← synthQPF F
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
  


open PrettyPrinter in
/--
  Elaborate the body of a qpf
-/
partial def elabQpf (vars : Array Q(Type u)) (target : Q(Type u)) (targetStx : Option Term := none) (normalized := false) : 
    TermElabM Term := do
  trace[QPF] "elabQPF :: {vars} -> {target}"
  let vars' := vars.toList;
  let arity : Nat := vars'.length;

  let varIds := vars'.map fun expr => expr.fvarId!
  let isLiveVar : FVarId → Bool
    := fun fvarId => (List.indexOf' fvarId varIds).isSome

  if target.isFVar && isLiveVar target.fvarId! then
    trace[QPF] f!"target {target} is a free variable"
    let ind ← match List.indexOf' target vars' with
    | none      => throwError "Free variable {target} is not one of the qpf arguments"
    | some ind  => pure ind

    let ind : Fin2 arity := ind.inv
    delab q(@Prj.{u} $arity $ind)

  else if !target.hasAnyFVar isLiveVar then
    trace[QPF] "target {target} is a constant"
    let stx ← delab q(Const.{u} $arity $target)
    trace[QPF] "represented by: {stx}"
    pure stx

  else if target.isApp then
    let ⟨_, F, args⟩ ← (Comp.parseApp isLiveVar target)
    let args := args.toList
    trace[QPF] "target {target} is an application of {F} to {args}"

    let F_stx ← delab F;
    trace[QPF] "F_stx := {F_stx}\nargs := {args}"

    /-
      Optimization: check if the application is of the form `F α β γ .. = F α β γ ..`.
      In such cases, we can directly return `F`, rather than generate a composition of projections.
    -/
    let is_trivial := 
      args.length == vars'.length
      && args.enum.all fun ⟨i, arg⟩ => 
          arg.isFVar && isLiveVar arg.fvarId! && vars'.indexOf arg == i
    if is_trivial then
      trace[QPF] "The application is trivial"
      return F_stx
    else
      let mut G : Array Term := #[]
      for a in args do
        let Ga ← elabQpf vars a none false
        G := G.push Ga
      trace[QPF] "F_stx := {F_stx}\nargs := {args}\nG := {G}"
      let comp ← `(Comp (n:=$(quote args.length)) $F_stx !![$G,*])
      trace[QPF] "comp := {comp}"
      pure comp

  else if target.isArrow then
    match target with
    | Expr.forallE _ e₁ e₂ .. => 
      let newTarget ← mkAppM ``MvQPF.Arrow.Arrow #[e₁, e₂]
      elabQpf vars newTarget targetStx normalized
    | _ => unreachable!

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
def elabQpfCompositionBody (view: QpfCompositionBodyView) : CommandElabM Term := do  
  trace[QPF] "elabQpfCompositionBody ::
    type?       := {view.type?}
    target      := {view.target}
    liveBinders := {view.liveBinders}
    deadBinders := {view.deadBinders}
  "
  -- runTermElabM fun _ => do
  liftTermElabM do
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
            elabQpf vars target_expr view.target


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
  let body ← elabQpfCompositionBody {
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
      def $F:ident $deadBinders:bracketedBinder* :
        CurriedTypeFun $live_arity := 
      TypeFun.curried $F_internal_applied

      $modifiers:declModifiers
      instance $deadBinders:bracketedBinder* : 
        MvQPF ($F_internal_applied) := 
      by unfold $F_internal; infer_instance
  )  
  trace[QPF] "cmd: {cmd}"
  elabCommand cmd


  let F_applied ← `($F $deadBinderNamedArgs:namedArgument*)

  let cmd ← `(command|
    $modifiers:declModifiers
    instance $deadBindersNoHoles:bracketedBinder* : 
      MvQPF (TypeFun.ofCurried $F_applied) 
    := MvQPF.instQPF_ofCurried_curried
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
