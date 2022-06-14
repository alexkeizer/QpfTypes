import Lean

open Lean Meta Core
open Lean.Elab.Command (InductiveView)
open Lean.Elab.Term (TermElabM)


structure DataType extends InductiveType where
  deriving Inhabited


structure Param where
  name : Expr
  type : Expr
  stx  : Syntax
  deriving Inhabited, Repr



namespace Param
  def type_as_univ_level (p : Param) : TermElabM Level := do
    let type ← inferType p.name;
    match type with
      | Expr.sort l .. => pure l
      | _              => throwError "Expected a sort as the type of parameter {p.name}"

  def to_binder_syntax (p : Param) : TermElabM Syntax := do
    let lvl ← p.type_as_univ_level
    let name := mkIdent p.name.fvarId!.name
    `( ($name : Sort $(quote lvl) ) )
end Param

/--
  `DataDecl` is a recreation of `Declaration.inductDecl`, meant for the `data` command
-/
structure DataDecl where
  (lparams  : List Name) 
  (nparams  : Nat) 
  (inner    : DataType)
  (view     : InductiveView)
  (isUnsafe : Bool)
  deriving Inhabited


def DataDecl.asInductDecl (self : DataDecl) : Declaration :=
  Declaration.inductDecl self.lparams self.nparams [self.inner.toInductiveType] self.isUnsafe



structure InternalMvFunctor :=
  (decl : Declaration)
  (induct : InductiveType)
  (def_name eqn_name map_name abs_name repr_name pfunctor_name : Name)
  (univ_params : List Level)
  (vec_lvl : Level)
  (live_params : List $ Expr × Nat)
  (dead_params : List $ Expr × Nat)
  (params : List Expr)
  (type : Expr)