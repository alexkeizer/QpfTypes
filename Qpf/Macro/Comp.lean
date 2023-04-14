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

/--
  Given an expression `e`, tries to find the largest subexpression `F` such that 
    * `e = F α₀ ... αₙ`, for some list of arguments `α_i`, and
    * `F` contains no live variables, and
    * `F` is a QPF
  Then, tries to infer an instance of `MvQPF (TypeFun.curried F)`
-/
protected def parseApp (isLiveVar : FVarId → Bool) (e : Expr) : TermElabM (Expr × (List Expr))
  := 
    if !e.isApp then
      throwError "application expected:\n {e}"
    else
      parseAppAux e List.nil none
where
  parseAppAux : Expr → List Expr → Option Exception → _
  | Expr.app F a, args, _ => do
    let args := a :: args
    let depth : Nat := args.length
    
    try
      -- Only try to infer QPF if `F` contains no live variables
      if !F.hasAnyFVar isLiveVar then
        /-
          HACK: For some reason building the following application directly with `Expr`s leads to
          weird universe issues. So, instead we build it with syntax.

          The original, `Expr` version was as follows:
            let F ← uncurry F (mkNatLit depth)
            let inst_type ← mkAppM ``MvQPF #[F];
        -/
        let u : Level ← mkFreshLevelMVar
        let F : Q(CurriedTypeFun.{u,u} $depth) := F
        trace[QPF] "F := {F}\ndepth := {depth}"
        let inst_type : Q(CurriedTypeFun.{u,u} $depth → TypeFun.{u,u} $depth) 
          := q(@TypeFun.ofCurried.{u,u} $depth)
        let inst_type : Q(TypeFun.{u,u} $depth)
          := .app inst_type F
        let inst_type : Q(Type (u+1))
          := q(MvQPF $inst_type)
        
        -- asserts that the instance exists, or throws an error
        let _inst ← synthInstance inst_type
        return (F, args)
      throwError "Smallest function subexpression still contains live variables:\n  {F}\ntry marking more variables as dead"
    catch e =>
      parseAppAux F args (some e)
    

  | _, _, some e => throw e
  | ex, _, none  => 
    if ex.hasAnyFVar isLiveVar then
      throwError "Smallest function subexpression still contains live variables:\n  {ex}\ntry marking more variables as dead"
    else
      throwError "Failed to infer an instance of `MvQPF ({ex})`, even though it is the smallest possible prefix expression"




def List.indexOf' {α : Type} [BEq α] :  α → (as : List α) → Option (Fin2 (as.length))
  | _, []       =>  none
  | a, b :: bs  =>  if a == b then
                      some .fz
                    else
                      match indexOf' a bs with
                      | none   => none
                      | some i => some <| .fs i


def Fin2.quote {n : Nat} : Fin2 n → Term
  | .fz   => mkCIdent ``Fin2.fz
  | .fs i => mkApp (mkCIdent ``Fin2.fs) #[quote i]

instance : {n : Nat} → Quote (Fin2 n) := ⟨Fin2.quote⟩


open Meta in
/-- Turns a vec of expressions `as` into an expr that represents `!![as,*]`-/
def Vec.exprOf (α : Q(Type u)) : {n : Nat} → Vec Q($α) n → Q(Vec $α $n)
  | 0, _ => q(Vec.nil)
  | _+1, as => 
    let a := as.last
    let as := exprOf α as.drop
    q(Vec.append1 $as $a)

  

open PrettyPrinter in
/--
  Elaborate the body of a qpf
-/
partial def elabQpf {u : Level} {n : Q(Nat)}
                    (vars : Array Q(Type u)) (target : Q(Type u)) (normalized := false) : 
      TermElabM Q(TypeFun.{u,u} $n) := do
  trace[QPF] "elabQPF :: {vars} -> {target}"
  let arity : Q(Nat) := mkNatLit vars.size
  
  let vars' := vars.toList;
  let varIds := vars'.map fun expr => expr.fvarId!
  let isLiveVar : FVarId → Bool
    := fun fvarId => (List.indexOf' fvarId varIds).isSome

  if target.isFVar && isLiveVar target.fvarId! then
    trace[QPF] f!"target {target} is a free variable"
    let index ← match List.indexOf' target vars' with
    | none      => throwError "Free variable {target} is not one of the qpf arguments"
    | some ind  => pure ind

    let index : Q(Fin2 $arity) ← elabTerm (quote (k:=`term) index.inv) none;
    let F := mkAppN (.const ``MvQPF.Prj ([u])) #[arity, index]
    return F

  else if !target.hasAnyFVar isLiveVar then
    trace[QPF] "target {target} is a constant"
    let F := mkAppN (.const ``MvQPF.Const ([u,u])) #[arity, target]
    trace[QPF] "represented by: {F}"
    pure F

  else if target.isApp then
    let (F, args) ← (Comp.parseApp isLiveVar target)
    trace[QPF] "target {target} is an application of {F} to {args}"

    /-
      Optimization: check if the application is of the form `F α β γ .. = F α β γ ..`.
      In such cases, we can directly return `F`, rather than generate a composition of projections.
    -/
    let is_trivial := 
      args.length == vars'.length
      && args.enum.all fun ⟨i, arg⟩ => 
          arg.isFVar && isLiveVar arg.fvarId! && vars'.indexOf arg == i
    if is_trivial && false then
      trace[QPF] "The application is trivial"
      return F
    else
      let mut G : Array Q(TypeFun.{u,u} $arity) := #[]
      for a in args do
        let Ga ← elabQpf vars a false
        G := G.push Ga
      trace[QPF] "G := {G}"
      let G_type : Q(Type (u+1)) := Expr.app (.const ``TypeFun ([u,u])) arity
      let G' := Vec.exprOf G_type (Vec.ofList G.toList)

      let comp ← mkAppM ``MvQPF.Comp #[F, G']
      trace[QPF] "comp := {comp}"
      pure comp

  else if target.isArrow then
    match target with
    | Expr.forallE _ e₁ e₂ .. => 
      let newTarget ← mkAppM ``MvQPF.Arrow.Arrow #[e₁, e₂]
      elabQpf vars newTarget normalized
    | _ => unreachable!

  else
    if !normalized then
      let target ← whnfR target
      elabQpf vars target true
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
def elabQpfCompositionBody (view: QpfCompositionBodyView) : CommandElabM Expr := do  
  trace[QPF] "elabQpfCompositionBody ::
    type?       := {view.type?}
    target      := {view.target}
    liveBinders := {view.liveBinders}
    deadBinders := {view.deadBinders}
  "
  -- runTermElabM fun _ => do
  liftTermElabM do
    let body_type ← 
      if let some typeStx := view.type? then
        let u ← mkFreshLevelMVar;
        trace[QPF] "Expected (Syntax): {typeStx}"
        let type ← elabTermEnsuringType typeStx (mkSort <| mkLevelSucc u)
        trace[QPF] "Expected (Expr): {type}"
        pure type
      else 
        let u ← mkFreshLevelMVar;
        pure <| mkSort <| mkLevelSucc u

    let u ← match body_type with
      | .sort (.succ v) => pure v
      | _ => 
        let stx : Syntax := view.type?.getD .missing
        throwErrorAt stx "invalid qpf, resulting type must be a type (e.g., `Type`, `Type _`, or `Type u`)"
  
    withAutoBoundImplicit <|
      elabBinders view.deadBinders fun _deadVars => 
        withLiveBinders view.liveBinders fun vars =>
          withoutAutoBoundImplicit <| do
            let target_expr ← elabTermEnsuringType view.target body_type;
            let n : Q(Nat) := mkNatLit vars.size
            @elabQpf u n vars target_expr false


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
  let body ← runTermElabM fun _ => delab body 
  
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
