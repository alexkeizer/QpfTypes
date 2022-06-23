import Qpf
import Qpf.Examples._02_QpfTree

open MvQpf


-- syntax "qpf " ident ident,+ " := " term : command

open Lean Elab Term Command Meta Syntax
open Parser (termParser)

-- #check Term.app


def parseApp : Expr → Option (Expr × (List Expr))
  | Expr.app F a _ =>
    match parseApp a with
    | some (G, args) => some (G, args ++ [a])
    | none =>
      none
  | _ => none

elab "qpf " F:ident αs:ident+ " := " target:term : command => do  
  let arity := αs.size;
  let arity_stx := mkNumLit arity.repr;

  let body ← liftTermElabM none $ do
    let u := mkLevelSucc <|← mkFreshLevelMVar;
    -- let v := mkLevelSucc <|← mkFreshLevelMVar;

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
        match parseApp expr with
        | none => throwError f!"No QPF found in {target}"
        | some (F, args) => 
          `(by sorry)

      
      else
        dbg_trace f!"Not FVar : {expr}"
        `(by sorry)
  
  let F_internal := mkIdent $ Name.mkStr F.getId "typefun";
  elabCommand <|<- `(def $F_internal : TypeFun $arity_stx := $body:term)
  elabCommand <|<- `(def $F := TypeFun.curried $F_internal)




class ToMvQpf (F : CurriedTypeFun n) where
  q : MvQpf (TypeFun.ofCurried F)



-- Projections
qpf F₁ α β γ := γ

#print F₁
#print F₁.typefun

#reduce F₁ Nat Int (List Nat)


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
#check F₁

qpf F₂ α β := (F₁ α) α β

#print F₁
#reduce F₁ ![Nat, Nat]
end Comp