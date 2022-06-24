import Qpf.Qpf

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
def parseApp (isLiveVar : FVarId → Bool) (e : Expr) : TermElabM (Expr × (List Expr))
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
      let F ← mkAppM ``TypeFun.ofCurried #[F]
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


def mkFin2Lit [Monad m] [MonadQuotation m] : Fin2 n → m Syntax
  | .fz   => `( Fin2.fz )
  | .fs i => do
    let i_stx ← mkFin2Lit i
    `( Fin2.fs $i_stx:term )


#check List.indexOf

open PrettyPrinter in
/--
  Elaborate the body of a qpf
-/
partial def elabQpf (vars : Array Expr) (target : Expr) (targetStx : Option Syntax := none) (normalized := false) : TermElabM Syntax := do
  let vars' := vars.toList;
  let arity := vars'.length;
  let arity_stx := mkNumLit arity.repr;

  let varIds := vars'.map fun expr => expr.fvarId!
  let isLiveVar : FVarId → Bool
    := fun fvarId => (List.indexOf' fvarId varIds).isSome

  if target.isFVar && isLiveVar target.fvarId! then
    dbg_trace f!"target {target} is a free variable"
    let ind ← match List.indexOf' target vars' with
    | none      => throwError "Free variable {target} is not one of the qpf arguments"
    | some ind  => pure ind

    dbg_trace "ind: {ind.toNat}"

    let ind_stx ← mkFin2Lit ind.inv;
    `(@Prj $arity_stx $ind_stx)

  else if !target.hasAnyFVar isLiveVar then
    dbg_trace f!"target {target} is a constant"
    let targetStx ← match targetStx with
      | some stx => pure stx
      | none     => delab target
    `(Const $arity_stx $targetStx)

  else if target.isApp then
    dbg_trace f!"target {target} is an application"
    let (F, args) ← (parseApp isLiveVar target)
    
    let mut G : Array Syntax := #[]
    for a in args do
      let Ga ← elabQpf vars a none false
      G := G.push Ga

    let F_stx ← delab F;
    `(Comp $F_stx ![$G,*])

  else
    if !normalized then
      let target ← whnfR target
      elabQpf vars target targetStx true
    else 
      throwError f!"Unexpected target expression :\n {target}"
    




def withLiveBinders [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
                [Inhabited α]
                (binders : Array Syntax) 
                (f : Array Expr → n α) : n α
:= do
  let u := mkLevelSucc <|← mkFreshLevelMVar;
  let decls := binders.map fun α => (
      α[0].getId, 
      fun _ => pure (mkSort u)
    )

  withLocalDeclsD decls f

#check Array
#check Syntax

elab "qpf " F:ident deadBinders:bracketedBinder* liveBinders:binderIdent+ " := " target:term : command => do  
  -- let deadBinders : Array Syntax := #[]

  dbg_trace "live_vars:\n {liveBinders}\n"
  if deadBinders.size > 0 then
    dbg_trace "dead_vars:\n {deadBinders}\n"

  let mut deadBindersNoHoles := #[]
  let mut deadBinderNames := #[]
  
  for stx in deadBinders do
    -- replace each hole with a fresh id
    let ids ← stx[1].getArgs.mapM fun id => do
      let kind := id.getKind
      if kind == identKind then
        return id
      else if kind == `Lean.Parser.Term.hole then
        mkFreshIdent id
      else 
        throwErrorAt id "identifier or `_` expected"
    
    for id in ids do
      deadBinderNames := deadBinderNames.push id

    let newStx := stx.setArg 1 (stx[1].setArgs ids)
    deadBindersNoHoles := deadBindersNoHoles.push newStx

  dbg_trace "dead_vars₂:\n {deadBinders}\n"


  let body ← liftTermElabM none $ do
    elabBinders deadBinders fun deadVars => 
      withLiveBinders liveBinders fun vars => do
        let target_expr ← elabTerm target none;
        elabQpf vars target_expr target

  /-
    Define the qpf using the elaborated body
  -/
  
  let F_internal := mkIdent $ Name.mkStr F.getId "typefun";
  
  let live_arity := mkNumLit liveBinders.size.repr;
  dbg_trace body
  elabCommand <|← `(
      def $F_internal $[$deadBinders]* : 
        TypeFun $live_arity := 
      $body:term
  )

  let F_internal_applied := mkApp (←`(@$F_internal)) deadBinderNames

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

  let F_applied := mkApp (←`(@$F)) deadBinderNames

  let cmd ← `(command|
    instance $[$deadBindersNoHoles]* : 
      MvQpf (TypeFun.ofCurried $F_applied) 
    := by unfold $F; infer_instance
  )
  dbg_trace cmd
  elabCommand cmd

end Macro.Comp
