import Qpf.Qpf
import Qpf.Macro.Common

namespace Macro.Comp
  open MvQpf
  open Lean Elab Term Command Meta
  open Syntax



/--
  Given an expression `e`, tries to find the largest subexpression `F` such that 
    * `e = F α₀ ... αₙ`, for some list of arguments `α_i` and
    * `F` contains no live variables
  Then, tries to infer an instance of `MvQpf (TypeFun.curried F)`
-/
protected def parseApp (isLiveVar : FVarId → Bool) (e : Expr) : TermElabM (Expr × (List Expr))
  := 
    if !e.isApp then
      throwError "application expected:\n {e}"
    else
      parseAppAux e
where
  parseAppAux : Expr → _
  | Expr.app F a _ => do
    -- If `F` contains live variables, recurse
    if F.hasAnyFVar isLiveVar then
      let (G, args) ← parseAppAux F;
      return (G, args ++ [a])
    else
      let F ← uncurry F
      let inst_type ← mkAppM ``MvQpf #[F];
      -- We don't need the instance, we just need to know it exists
      let _ ← synthesizeInst inst_type    
        
      return (F, [a])

  | ex => 
    throwError "Smallest function subexpression still contains live variables:\n  {ex}\ntry marking more variables as dead "




def List.indexOf' {α : Type} [inst : BEq α] :  α → (as : List α) → Option (Fin2 (as.length))
  | _, []       =>  none
  | a, b :: bs  =>  if a == b then
                      some .fz
                    else
                      match indexOf' a bs with
                      | none   => none
                      | some i => some <| .fs i


def Fin2.quote {n : Nat} : Fin2 n → Syntax 
  | .fz   => mkCIdent ``Fin2.fz
  | .fs i => mkApp (mkCIdent ``Fin2.fs) #[quote i]

instance : {n : Nat} → Quote (Fin2 n) := ⟨Fin2.quote⟩
  


open PrettyPrinter in
/--
  Elaborate the body of a qpf
-/
partial def elabQpf (vars : Array Expr) (target : Expr) (targetStx : Option Syntax := none) (normalized := false) : TermElabM Syntax := do
  let vars' := vars.toList;
  let arity := vars'.length;
  let arity_stx := quote arity;

  let varIds := vars'.map fun expr => expr.fvarId!
  let isLiveVar : FVarId → Bool
    := fun fvarId => (List.indexOf' fvarId varIds).isSome

  if target.isFVar && isLiveVar target.fvarId! then
    dbg_trace f!"target {target} is a free variable"
    let ind ← match List.indexOf' target vars' with
    | none      => throwError "Free variable {target} is not one of the qpf arguments"
    | some ind  => pure ind

    let ind_stx := quote ind.inv;
    `(@Prj $arity_stx $ind_stx)

  else if !target.hasAnyFVar isLiveVar then
    dbg_trace f!"target {target} is a constant"
    let targetStx ← match targetStx with
      | some stx => pure stx
      | none     => delab target
    `(Const $arity_stx $targetStx)

  else if target.isApp then
    dbg_trace f!"target {target} is an application"
    let (F, args) ← (Comp.parseApp isLiveVar target)
    
    let mut G : Array Syntax := #[]
    for a in args do
      let Ga ← elabQpf vars a none false
      G := G.push Ga

    let F_stx ← delab F;
    `(Comp $F_stx ![$G,*])

  else if target.isArrow then
    match target with
    | Expr.forallE _ e₁ e₂ .. => 
      let newTarget ← mkAppM ``MvQpf.Arrow.Arrow #[e₁, e₂]
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
    


elab "qpf " F:ident sig:optDeclSig " := " target:term : command => do  
  dbg_trace sig
  let (liveBinders, deadBinders) ← splitLiveAndDeadBinders sig[0].getArgs

  dbg_trace "live_vars:\n {liveBinders}\n"
  if deadBinders.size > 0 then
    dbg_trace "dead_vars:\n {deadBinders}\n"

  let (deadBindersNoHoles, deadBinderNames) ← mkFreshNamesForBinderHoles deadBinders

  dbg_trace "dead_vars_no_holes:\n {deadBindersNoHoles}\n"
  
  let body ← liftTermElabM none $ do
    let body_type ← 
      if let some sigInner := sig[1].getOptional? then
        let u ← mkFreshLevelMVar;
        dbg_trace sigInner
        dbg_trace sigInner[1]
        let type ← elabTermEnsuringType sigInner[1] (mkSort <| mkLevelSucc u)
        if !(←whnf type).isType then
          throwErrorAt sigInner[1] "invalid qpf, resulting type must be a type (e.g., `Type`, `Type _`, or `Type u`)"
        pure type
      else 
        let u ← mkFreshLevelMVar;
        pure <| mkSort <| mkLevelSucc u
  
    withAutoBoundImplicit <|
      elabBinders deadBinders fun deadVars => 
        withLiveBinders liveBinders fun vars =>
          withoutAutoBoundImplicit <| do
            let target_expr ← elabTermEnsuringType target body_type;
            elabQpf vars target_expr target

  /-
    Define the qpf using the elaborated body
  -/
  
  let F_internal := mkIdent $ Name.mkStr F.getId "typefun";
  
  let live_arity := mkNumLit liveBinders.size.repr;
  -- dbg_trace body
  elabCommand <|← `(
      def $F_internal $[$deadBinders]* : 
        TypeFun $live_arity := 
      $body:term
  )

  let deadBinderNamedArgs ← deadBinderNames.mapM fun n => `(Parser.Term.namedArgument| ($n:ident := $n:term))
  let F_internal_applied := mkApp F_internal deadBinderNamedArgs

  let cmd ← `(
      def $F $[$deadBinders]* :
        CurriedTypeFun $live_arity := 
      TypeFun.curried $F_internal_applied

      instance $[$deadBinders]* : 
        MvQpf ($F_internal_applied) := 
      by unfold $F_internal; infer_instance
  )  
  -- dbg_trace cmd
  elabCommand cmd

  let F_applied := mkApp F deadBinderNamedArgs

  let cmd ← `(command|
    instance $[$deadBindersNoHoles]* : 
      MvQpf (TypeFun.ofCurried $F_applied) 
    := by unfold $F; infer_instance
  )
  -- dbg_trace cmd
  elabCommand cmd

end Macro.Comp
