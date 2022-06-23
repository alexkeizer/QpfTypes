import Qpf
import Qpf.Examples._02_Tree

open MvQpf


-- syntax "qpf " ident ident,+ " := " term : command

open Lean Elab Term Command Meta
open Parser (termParser)

#check Lean.throwError


open Lean in
def parseApp : Expr → TermElabM (Expr × Expr × (List Expr))
  | Expr.app F a _ => do
    try
      let (q, G, args) ← parseApp F;
      pure (q, G, args ++ [a])
    catch e₁ =>
      try
        let n_mvar ← mkFreshExprMVar (mkConst ``Nat)
        let us ← mkFreshLevelMVars 2

        -- let F_type := mkApp (mkConst ``CurriedTypeFun us) n_mvar;
        -- let F ← elabTermEnsuringType F F_type;

        let inst ← synthesizeInst <|← mkAppM ``ToMvQpf #[F]

        pure (inst, F, [a])
      catch e₂ =>
        throw e₁
    

  | ex => throwError "expression should be an application: {ex}"


open Syntax in
def elabQpf (αs : Array Syntax) (target : Syntax) : TermElabM Syntax := do
  let arity := αs.size;
  let arity_stx := mkNumLit arity.repr;

  let u := mkLevelSucc <|← mkFreshLevelMVar;
  let decls := αs.map fun α => (α.getId, fun _ => pure (mkSort u))

  withLocalDeclsD decls fun vars => do
      let expr ← elabTerm target none;

      if expr.isFVar then
        dbg_trace f!"target {expr} is a free variable"
        let ind := vars.toList.indexOf expr;        
        let ind_stx   := mkNumLit (arity - ind - 1).repr;
        `(Prj $ind_stx)

      else if !expr.hasFVar then
        dbg_trace f!"target {expr} is a constant"
        `(Const $arity_stx $target)

      else if expr.isApp then
        dbg_trace f!"target {expr} is an application"
        let (inst, F, args) ← (parseApp expr)  -- <|> throwError f!"No QPF found in {expr}"
        `(by sorry)

      else
        dbg_trace f!"Not FVar : {expr}"
        `(by sorry)

open Syntax in
elab "qpf " F:ident αs:ident+ " := " target:term : command => do  
  let arity := αs.size;
  let arity_stx := mkNumLit arity.repr;

  let body ← liftTermElabM none $ elabQpf αs target
  
  let F_internal := mkIdent $ Name.mkStr F.getId "typefun";
  elabCommand <|<- `(
      def $F_internal : TypeFun $arity_stx := $body:term

      def $F := TypeFun.curried $F_internal

      instance : MvQpf $F_internal := by unfold $F_internal; infer_instance

      instance : ToMvQpf $F := by unfold $F; infer_instance
  )




-- Projections
qpf F₁ α β γ := γ
qpf F₂ α β γ := α

#print F₁
#print F₁.typefun

#print F₂
#print F₂.typefun

#reduce F₁.typefun ![Nat, Int, (List Nat)]
#reduce F₁ Nat Int (List Nat)


#reduce F₂ Nat Int (List Nat)


-- Constants
qpf F_int α β := Int

#print F_int
#print F_int.typefun

#reduce F_int Nat Nat

qpf F_tree α β := QpfTree Nat

#print F_tree
#print F_tree.typefun

#reduce F_tree Nat Nat


-- Composition
qpf F₃ α β := F₁ α α β

-- #print F₁
-- #reduce F₁ ![Nat, Nat]


#check mkAppM
#check mkAppN

-- elab "impl_mvqpf " F:ident : term => do
  


#check (inferInstance : MvQpf F₁.typefun)
#check (inferInstance : ToMvQpf F₁)

#check impl_mvqpf F₁
#check impl_mvqpf Nat

#check (inferInstance : ToMvQpf F₁)