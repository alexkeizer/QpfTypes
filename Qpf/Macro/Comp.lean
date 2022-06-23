import Qpf.Qpf

namespace Macro.Comp
  open MvQpf
  open Lean Elab Term Command Meta
  open Syntax


/--
  Given an expression `e`, tries to find the smallest expression `F` such that 
    * `e = F α₀ ... αₙ`, for some list of arguments `αᵢ` and
    * `F` contains no live variables, and
    * there is an instance of `MvQpf F`
-/
def parseApp : Expr → TermElabM (Expr × (List Expr))
  | Expr.app F a _ => do
    try
      let (G, args) ← parseApp F;
      pure (G, args ++ [a])
    catch e₁ =>
      -- We only try to see if `F` is a QPF if it does not depend on live variables
      if F.hasFVar then
        throw e₁
      else try
        let F ← mkAppM ``TypeFun.ofCurried #[F]
        let inst_type ← mkAppM ``MvQpf #[F];
        -- We don't need the instance, we just need to know it exists
        let _ ← synthesizeInst inst_type    
        
        pure (F, [a])
      catch e₂ =>
        throwError "{e₁.toMessageData}\n\n{e₂.toMessageData}"    

  | ex => 
    throwError "expected application:\n  {ex}"


#check List.indexOf


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



open PrettyPrinter in
partial def elabQpf (vars : Array Expr) (target : Expr) (targetStx : Option Syntax := none) : TermElabM Syntax := do
  let vars' := vars.toList;
  let arity := vars'.length;
  let arity_stx := mkNumLit arity.repr;

  if target.isFVar then
    dbg_trace f!"target {target} is a free variable"
    let ind ← match List.indexOf' target vars' with
    | none      => throwError "Free variable {target} is not one of the qpf arguments"
    | some ind  => pure ind

    dbg_trace "ind: {ind.toNat}"

    let ind_stx ← mkFin2Lit ind.inv;
    `(@Prj $arity_stx $ind_stx)

  else if !target.hasFVar then
    dbg_trace f!"target {target} is a constant"
    let targetStx ← match targetStx with
      | some stx => pure stx
      | none     => delab target
    `(Const $arity_stx $targetStx)

  else if target.isApp then
    dbg_trace f!"target {target} is an application"
    let (F, args) ← (parseApp target)
    
    let mut G : Array Syntax := #[]
    for a in args do
      let Ga ← elabQpf vars a
      G := G.push Ga

    let F_stx ← delab F;
    `(Comp $F_stx ![$G,*])

  else
    throwError f!"Unexpected target expression :\n {target}"



def withBinders [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
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
  

-- elab "qpf " F:ident dead_binders:bracketedBinder* live_binders:binderIdent+ " := " target:term : command => do  
elab "#qpf " F:ident live_binders:binderIdent+ " := " target:term : command => do  
  let dead_binders : Array Syntax := #[]

  dbg_trace "live_vars:\n {live_binders}\n"
  if dead_binders.size > 0 then
    dbg_trace "dead_vars:\n {dead_binders}\n"
  
  let body ← liftTermElabM none $ do    
    withBinders live_binders fun vars => do
      let target_expr ← elabTerm target none;
      elabQpf vars target_expr target
  
  let F_internal := mkIdent $ Name.mkStr F.getId "typefun";
  
  let live_arity := mkNumLit live_binders.size.repr;
  dbg_trace body
  let cmd ← `(
      def $F_internal $[$dead_binders]* : 
        TypeFun $live_arity := 
      $body:term

      def $F $[$dead_binders]* :
        CurriedTypeFun $live_arity := 
      TypeFun.curried $F_internal

      instance instInternal : MvQpf $F_internal := by unfold $F_internal; infer_instance
  )  
  elabCommand cmd
  try
    -- It seems that `instInternal` can be used as-is for the uncurried version of `F`
    elabCommand <|← `(command|
      instance : MvQpf (TypeFun.ofCurried $F) := instInternal
    )
  catch e =>
    -- However, if that fails, we try again through by infering an instance
    elabCommand <|← `(command|
      instance : MvQpf (TypeFun.ofCurried $F) := by unfold $F; infer_instance
    )
end Macro.Comp